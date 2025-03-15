import Mathlib

open CategoryTheory Set Topology Opposite Quiver Hom

universe u

@[ext]
structure Opens (X : Type u) [TopologicalSpace X] where
  carrier : Set X
  isOpen : IsOpen carrier

-- Note: this single instance gives `Opens X` access to a Mem instance, a Preorder instance, and a SmallCategory instance
instance (X : Type u) [TopologicalSpace X] : SetLike (Opens X) X where
  coe := Opens.carrier
  coe_injective' := λ _ _ ↦ Opens.ext

instance (X : Type u) [TopologicalSpace X] : Inf (Opens X) := ⟨λ U V ↦ ⟨U.carrier ∩ V.carrier, IsOpen.inter U.2 V.2⟩⟩

lemma inf_carrier_def (X : Type u) [TopologicalSpace X] {U V : Opens X} : (U ⊓ V).carrier = U.carrier ∩ V.carrier := rfl

instance (X : Type u) [TopologicalSpace X] : Sup (Opens X) := ⟨λ U V ↦ ⟨U.carrier ∪ V.carrier, IsOpen.union U.2 V.2⟩⟩

instance (X : Type u) [TopologicalSpace X] : SupSet (Opens X) := ⟨λ S ↦ ⟨⋃₀ (Opens.carrier '' S), isOpen_sUnion (λ _ ⟨i, hi⟩ ↦ hi.2 ▸ i.2)⟩⟩

-- Presheafs are naturally of sets, and the concept of a sheaf of rings is handled elsewhere (in the notion of a ringed space).
def myPresheaf (X : Type u) [TopologicalSpace X] := (Opens X)ᵒᵖ ⥤ Type u

namespace myPresheaf

/-- `ℱ.sect U` is the type of sections of `U`. -/
abbrev sect {X : Type u} [TopologicalSpace X] (ℱ : myPresheaf X) (U : Opens X) := ℱ.obj ⟨U⟩

/-- `ℱ.res s huv` is the restriction of the section `s : ℱ.sect U` to `ℱ.sect V`, where `huv` is a proof that `V ≤ U`. -/
abbrev res {X : Type u} [TopologicalSpace X] {ℱ : myPresheaf X} {U V : Opens X} (s : sect ℱ U) (huv : V ≤ U) := ℱ.map (homOfLE huv).op s

variable {X : Type u} [TopologicalSpace X] {ℱ : myPresheaf X}

theorem res_comp {U V W : Opens X} (s : sect ℱ U) (huv : V ≤ U) (hvw : W ≤ V) : res (res s huv) hvw = res s (le_trans hvw huv) := by
  have : (ℱ.map (homOfLE hvw).op) ((ℱ.map (homOfLE huv).op) s) = ℱ.map ((homOfLE huv).op ≫ (homOfLE hvw).op) s
  rw [ℱ.map_comp]; rfl
  simp_rw [res, this]; rfl

-- theorem res_zero {U V : Opens X} (huv : V ≤ U) : res (0 : sect ℱ U) huv = 0 := by
--   rw [res, map_zero]

-- theorem res_add {U V : Opens X} (s t : sect ℱ U) (huv : V ≤ U) : res (s + t) huv = (res s huv) + (res t huv) := by
--   rw [res, map_add]

-- theorem res_sub {U V : Opens X} (s t : sect ℱ U) (huv : V ≤ U) : res (s - t) huv = (res s huv) - (res t huv) := by
--   rw [res, map_sub]

-- theorem res_mul {U V : Opens X} (s t : sect ℱ U) (huv : V ≤ U) : res (s*t) huv = (res s huv) * (res t huv) := by
--   rw [res, map_mul]

theorem inf_le_left {U V : Opens X} : U ⊓ V ≤ U := inter_subset_left
theorem inf_le_right {U V : Opens X} : U ⊓ V ≤ V := inter_subset_right
-- A terribly inefficient proof that I don't care to update
theorem le_iSup {ι : Type} {U : ι → Opens X} (i : ι) : U i ≤ ⨆ j, U j := by
  intro x hx
  use (U i).carrier
  constructor
  rw [mem_image]
  use U i
  constructor
  use i
  rfl
  exact hx

universe v

def Compatible {ι : Type v} {U : ι → Opens X} (s : (i : ι) → sect ℱ (U i)) := ∀ i j, res (s i) inf_le_left = res (s j) inf_le_right

theorem compatible_of_res {ι : Type v} {U : ι → Opens X} (s : sect ℱ (⨆ j, U j)) : Compatible (λ i ↦ res s (le_iSup i)) := by
  intro i j
  simp_rw [res_comp]

-- Tara's other idea
class IsSheaf (ℱ : myPresheaf X) : Prop where
  glueing' : ∀ {ι : Type v} {U : ι → Opens X} (s : (i : ι) → sect ℱ (U i)) (hs : Compatible s), ∃! s', ∀i, res s' (le_iSup i) = s i

class IsSeparated (ℱ : myPresheaf X) : Prop where
  locality' : ∀ {ι : Type v} {U : ι → Opens X} (s t : ℱ.sect (⨆ i, U i)) (hi : ∀i : ι, res s (le_iSup i) = res t (le_iSup i)), s = t

class IsGlueable (ℱ : myPresheaf X) : Prop where
  glueing' : ∀ {ι : Type v} {U : ι → Opens X} {s : (i : ι) → sect ℱ (U i)} (hs : Compatible s), ∃ s', ∀i, res s' (le_iSup i) = s i

#check Over

-- example : IsSheaf ℱ ↔ IsSeparated ℱ ∧ IsGlueable ℱ := by
--   constructor <;> intro hf
--   constructor <;> constructor
--   intro ι U s t hi
--   let r := hf.glueing' (λ i ↦ ℱ.res s (@le_iSup _ _ U i))

-- theorem glueing {ℱ : myPresheaf X} [inst : IsSheaf ℱ] : ∀ {ι : Type _} {U : ι → Opens X} {s : (i : ι) → sect ℱ (U i)}, (hs : Compatible s) → ∃! s', ∀i, res s' (le_iSup i) = s i := IsSheaf.glueing'

-- def locality

-- variable {𝒪 : myPresheaf X} [inst : IsSheaf 𝒪]

-- theorem locality_zero {ι : Type _} {U : ι → Opens X} (s : sect 𝒪 (⨆ i, U i)) (hs : ∀i, res s (le_iSup i) = 0) : s = 0 := by
--   let ⟨t', ht'⟩ := glueing (compatible_of_res s)
--   have : s = t'
--   apply ht'.2
--   intro i; rfl
--   rw [this]
--   have : 0 = t'
--   apply ht'.2
--   intro i
--   rw [res_zero, hs]
--   exact this.symm

-- theorem locality {ι : Type _} {U : ι → Opens X} (s t : sect 𝒪 (⨆ i, U i)) (hs : ∀i, res s (le_iSup i) = res t (le_iSup i)) : s = t := by
--   have : ∀i, res (s - t) (le_iSup i) = 0
--   intro i
--   rw [res_sub, sub_eq_zero]
--   exact hs i
--   have h : s - t = 0 := @locality_zero _ _ _ inst _ _ (s-t) this
--   rw [← sub_eq_zero]
--   exact h
