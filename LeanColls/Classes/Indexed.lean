/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Ops
import LeanColls.Classes.IndexType

namespace LeanColls

/-! ## Indexed Collections

This file defines [Indexed] collections, which are indexed by some type `ι`.
The math model for indexed collections is a total function `ι → α`.

**Note:** technically [Indexed] does not require `ι` to be [IndexType],
but a lawful [Indexed] instance implies an [IndexType] instance on `ι`.
-/

class Indexed (C : Type u) (ι : outParam (Type v)) (τ : outParam (Type w))
  extends
    Membership τ C,
    ToMultiset C τ,
    Fold C (ι × τ),
    Size C
   where
  /-- Form an instance of the collection type by
    specifying its value at every index. -/
  ofFn : (ι → τ) → C
  /-- Get the value of a collection at an index. -/
  get : C → ι → τ
  /-- Apply a function at an index (often done in-place). -/
  update : C → ι → (τ → τ) → C
  /-- Set the value of the function at an index -/
  set : C → ι → τ → C := (update · · <| Function.const _ ·)
  size c := fold c (fun acc _ => acc + 1) 0

class LawfulIndexed (C ι τ) [DecidableEq ι] [Indexed C ι τ] where
  get_ofFn : ∀ f, Indexed.get (Indexed.ofFn (C := C) f) = f
  get_set : ∀ (c : C) i a j,
    Indexed.get (Indexed.set c i a) j =
      if i = j then a else Indexed.get c j
  get_update : ∀ (c : C) i f j,
    Indexed.get (Indexed.update c i f) j =
      if i = j then f (Indexed.get c j) else Indexed.get c j

namespace Indexed

variable [Indexed C ι τ] [DecidableEq ι] [LawfulIndexed C ι τ]

@[simp] theorem get_set_eq (c : C)
  : Indexed.get (Indexed.set c i a) i = a := by
  rw [LawfulIndexed.get_set]; simp

@[simp] theorem get_set_ne (c : C) (h : i ≠ j)
  : Indexed.get (Indexed.set c i a) j = Indexed.get c j := by
  rw [LawfulIndexed.get_set]; simp [h]

@[simp] theorem get_update_eq (c : C)
  : Indexed.get (Indexed.update c i f) i = f (Indexed.get c i) := by
  rw [LawfulIndexed.get_update]; simp

@[simp] theorem get_update_ne (c : C) (h : i ≠ j)
  : Indexed.get (Indexed.update c i a) j = Indexed.get c j := by
  rw [LawfulIndexed.get_update]; simp [h]

export LawfulIndexed (get_ofFn)
attribute [simp] get_ofFn