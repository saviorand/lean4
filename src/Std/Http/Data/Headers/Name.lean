/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.ToString
public import Std.Http.Internal
import Init.Data.String.Search
import Init.Data.String.Iter
import Init.Data.String.Lemmas.Modify
import Init.Data.String.Lemmas.Iter
import Init.Data.String.Lemmas.Intercalate
import Init.Data.String.Lemmas.Pattern.Split.Char
import Init.Data.Iterators.Lemmas.Combinators.FilterMap
import Init.Data.List.SplitOn.Lemmas

public section

/-!
# Header Names

This module defines the `Name` type, which represents validated HTTP header names that conform to
HTTP standards.

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#section-5
-/

namespace Std.Http.Header

set_option linter.all true

open Std.Http.Internal

/--
Proposition asserting that a string is a valid HTTP header name: all characters are valid token
characters and the string is non-empty.

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#name-field-names
-/
abbrev IsValidHeaderName (s : String) : Prop :=
  isToken s

/--
A validated HTTP header name that ensures all characters conform to HTTP standards. Header names are
case-insensitive according to HTTP specifications.

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#name-field-names
-/
@[ext]
structure Name where
  /--
  The lowercased normalized header name string.
  -/
  value : String

  /--
  The proof that it's a valid header name.
  -/
  isValidHeaderValue : IsValidHeaderName value := by decide

  /--
  The proof that we stored the header name in stored as a lower case string.
  -/
  isLowerCase : IsLowerCase value := by decide
deriving Repr, DecidableEq

namespace Name

instance : BEq Name where
  beq a b := a.value = b.value

instance : Hashable Name where
  hash x := Hashable.hash x.value

theorem beq_eq {x y : Name} : (x == y) = (x.value == y.value) :=
  rfl

set_option linter.extra.dupNamespace false in
@[deprecated Header.Name.beq_eq (since := "2026-06-04")]
theorem Name.beq_eq {x y : Name} : (x == y) = (x.value == y.value) :=
  Header.Name.beq_eq

instance : LawfulBEq Name where
  rfl {x} := by simp [beq_eq]
  eq_of_beq {x y} := by grind [beq_eq, Name.ext]

instance : LawfulHashable Name := inferInstance

instance : Inhabited Name where
  default := ⟨"_", by decide, by decide⟩

/--
Attempts to create a `Name` from a `String`, returning `none` if the string contains invalid
characters for HTTP header names or is empty.
-/
def ofString? (s : String) : Option Name :=
  let val := s.trimAscii.toString.toLower
  if h : IsValidHeaderName val ∧ IsLowerCase val then
    some ⟨val, h.left, h.right⟩
  else
    none

/--
Creates a `Name` from a string, panicking with an error message if the string contains invalid
characters for HTTP header names or is empty.
-/
def ofString! (s : String) : Name :=
  match ofString? s with
  | some res => res
  | none => panic! s!"invalid header name: {s.quote}"

/--
Converts the header name to title case (e.g., "Content-Type").

Note: some well-known headers have unconventional casing (e.g., "WWW-Authenticate"),
but since HTTP header names are case-insensitive, this always uses simple capitalization.
-/
@[inline]
def toCanonical (name : Name) : String :=
  let it := name.value.split '-'
    |>.map (·.copy.capitalize)

  it.intercalateString "-"

/--
Performs a case-insensitive comparison between a `Name` and a `String`. Returns `true` if they match.
-/
@[expose]
def is (name : Name) (s : String) : Bool :=
  name.value == s.toLower

theorem cr_not_mem (n : Name) : '\r' ∉ n.value.toList :=
  fun h => absurd (List.all_eq_true.mp (of_decide_eq_true n.isValidHeaderValue).2 _ h) (by decide)

theorem lf_not_mem (n : Name) : '\n' ∉ n.value.toList :=
  fun h => absurd (List.all_eq_true.mp (of_decide_eq_true n.isValidHeaderValue).2 _ h) (by decide)

private theorem Char.toLower_toUpper (c : Char) : c.toUpper.toLower = c.toLower := by
  have hb := c.val.toNat_lt
  simp only [Char.toUpper]
  split
  · next h =>
    have ⟨h₁, h₂⟩ := h
    simp only [Char.toLower]
    split <;> split
    all_goals
      next h₃ h₄ =>
      have h₃' := h₃
      have h₄' := h₄
      simp only [Char.ext_iff, show 'a'.val = 97 from rfl, show 'z'.val = 122 from rfl,
        show 'A'.val = 65 from rfl, show 'Z'.val = 90 from rfl, UInt32.le_iff_toNat_le,
        UInt32.toNat_add, UInt32.toNat_ofNat, UInt32.reduceSub, ge_iff_le,
        ← UInt32.toNat_inj] at h₁ h₂ h₃' h₄' ⊢
      omega
  · rfl

private theorem map_toLower_capitalize (s : String) :
    s.capitalize.toList.map Char.toLower = s.toList.map Char.toLower := by
  rw [String.toList_capitalize]
  split <;> simp_all [Char.toLower_toUpper]

/--
The canonical form that is written to the wire differs from the stored name only in letter case.
-/
theorem toLower_toCanonical (n : Name) : n.toCanonical.toLower = n.value := by
  conv => rhs; rw [← n.isLowerCase]
  apply String.toList_inj.mp
  have hsplit := String.toList_split_char (s := n.value) (c := '-')
  simp only [toCanonical, String.toLower, String.toList_map, Std.Iter.intercalateString_eq,
    Std.Iter.toList_map, String.toList_intercalate, List.map_intercalate, List.map_map]
  have hf : ((fun x => List.map Char.toLower x) ∘ String.toList ∘ toString ∘
      fun x : String.Slice => x.copy.capitalize) =
      (fun s : String => s.toList.map Char.toLower) ∘ String.Slice.copy := by
    funext x
    simp only [Function.comp_apply, toString]
    exact map_toLower_capitalize x.copy
  rw [hf, ← List.map_map, hsplit, List.map_map]
  conv => rhs; rw [← List.intercalate_splitOn '-' (xs := n.value.toList), List.map_intercalate]
  simp [Function.comp_def]

theorem cr_not_mem_toCanonical (n : Name) : '\r' ∉ n.toCanonical.toList := by
  have := n.cr_not_mem
  rw [← n.toLower_toCanonical, String.toLower, String.toList_map] at this
  exact fun h => this (List.mem_map.mpr ⟨_, h, rfl⟩)

theorem lf_not_mem_toCanonical (n : Name) : '\n' ∉ n.toCanonical.toList := by
  have := n.lf_not_mem
  rw [← n.toLower_toCanonical, String.toLower, String.toList_map] at this
  exact fun h => this (List.mem_map.mpr ⟨_, h, rfl⟩)

instance : ToString Name where
  toString name := name.toCanonical

/--
Standard Content-Type header name
-/
def contentType : Header.Name := .mk "content-type"

/--
Standard Content-Length header name
-/
def contentLength : Header.Name := .mk "content-length"

/--
Standard Host header name
-/
def host : Header.Name := .mk "host"

/--
Standard Authorization header name
-/
def authorization : Header.Name := .mk "authorization"

/--
Standard User-Agent header name
-/
def userAgent : Header.Name := .mk "user-agent"

/--
Standard Accept header name
-/
def accept : Header.Name := .mk "accept"

/--
Standard Connection header name
-/
def connection : Header.Name := .mk "connection"

/--
Standard Transfer-Encoding header name
-/
def transferEncoding : Header.Name := .mk "transfer-encoding"

/--
Standard Server header name
-/
def server : Header.Name := .mk "server"

/--
Standard Date header name
-/
def date : Header.Name := .mk "date"

/--
Standard Expect header name
-/
def expect : Header.Name := .mk "expect"

/--
Standard Cookie header name (client → server)
-/
def cookie : Header.Name := .mk "cookie"

/--
Standard Set-Cookie header name (server → client)
-/
def setCookie : Header.Name := .mk "set-cookie"

/--
Standard Location header name
-/
def location : Header.Name := .mk "location"

/--
Standard Proxy-Authorization header name
-/
def proxyAuthorization : Header.Name := .mk "proxy-authorization"

/--
Standard Content-Encoding header name
-/
def contentEncoding : Header.Name := .mk "content-encoding"

/--
Standard Content-Language header name
-/
def contentLanguage : Header.Name := .mk "content-language"

/--
Standard Content-Location header name
-/
def contentLocation : Header.Name := .mk "content-location"

/--
Standard Last-Modified header name
-/
def lastModified : Header.Name := .mk "last-modified"

/--
Standard Referer header name
-/
def referer : Header.Name := .mk "referer"

/--
Standard Origin header name
-/
def origin : Header.Name := .mk "origin"

/--
Standard Keep-Alive header name
-/
def keepAlive : Header.Name := .mk "keep-alive"

/--
Standard If-None-Match header name
-/
def ifNoneMatch : Header.Name := .mk "if-none-match"

/--
Standard If-Modified-Since header name
-/
def ifModifiedSince : Header.Name := .mk "if-modified-since"

end Std.Http.Header.Name
