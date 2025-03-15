import Mathlib

variable (X : Type*)

-- class Geometry where
--   seg : X → X → Set X
--   congr : X → X → X → X → Prop
--   congr_refl : ∀x y, congr x y y x
--   congr_id : ∀x y z, congr x y z z → x = y
--   congr_trans : ∀ u v w x y z, congr x y z u → congr x y v w → congr z u v w
--   seg_id : ∀x y, y ∈ seg x x → y = x
--   seg_pasch : ∀ u v x y z, u ∈ seg x z → v ∈ seg y z → ∃a, a ∈ seg u y ∧ a ∈ seg v x

-- class Geometry where
--   IsLine : Set X → Prop
--   point_line : ∀P Q, P ≠ Q → ∃! l, IsLine l ∧ P ∈ l ∧ Q ∈ l
--   line_measure :
