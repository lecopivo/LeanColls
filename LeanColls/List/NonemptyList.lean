/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.List.Basic

open LeanColls

structure NonemptyList (α) where
  hd : α
  tl : List α

namespace NonemptyList

instance : Foldable (NonemptyList α) α where
  fold := λ ⟨hd,tl⟩ f acc => tl.foldl f (f acc hd)