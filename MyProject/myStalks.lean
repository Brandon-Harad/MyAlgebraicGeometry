import Mathlib
import MyProject.mySheafTheory

variable {X : Type*} [TopologicalSpace X] (F : myPresheaf X)

structure OpenNhds (x : X) where
  toOpens : Opens X
  mem : x ∈ toOpens

structure myPrestalk (x : X) where
  nhd : OpenNhds x
  sect : F.sect nhd.toOpens

lemma le_left_of_le_inf {U V W : Opens X} (hw : W ≤ U ⊓ V) : W ≤ U := le_trans hw (myPresheaf.inf_le_left)
lemma le_right_of_le_inf {U V W : Opens X} (hw : W ≤ U ⊓ V) : W ≤ V := le_trans hw (myPresheaf.inf_le_right)

def eventuallyEqual (x : X) (s t : myPrestalk F x) := ∃V : {V // x ∈ V ∧ V ≤ s.1.1 ⊓ t.1.1}, F.res s.sect (le_left_of_le_inf V.2.2) = F.res t.sect (le_right_of_le_inf V.2.2)

lemma myinf_comm {U V : Opens X} : U ⊓ V = V ⊓ U := by
  apply Opens.ext
  simp_rw [inf_carrier_def, Set.inter_comm]
lemma le_of_inf_rfl {U : Opens X} : U ≤ U ⊓ U := λ _ h ↦ ⟨h, h⟩
lemma le_of_le_of_inf_rfl {U V : Opens X} (hu : U ≤ V) : U ≤ V ⊓ V := λ _ h ↦ ⟨hu h, hu h⟩
lemma comm_of_le_of_inf {U V W : Opens X} (h : U ≤ V ⊓ W) : U ≤ W ⊓ V := by rwa [myinf_comm]
lemma mem_inf {U V : Opens X} {x : X} (hu : x ∈ U) (hv : x ∈ V) : x ∈ U ⊓ V := ⟨hu, hv⟩
lemma inf_le_inf_trans {U₁ U₂ V₁ V₂ V₃ : Opens X} (hu₁ : U₁ ≤ V₁ ⊓ V₂) (hu₂ : U₂ ≤ V₂ ⊓ V₃) : U₁ ⊓ U₂ ≤ V₁ ⊓ V₃ := λ _ hx ↦ ⟨(hu₁ hx.1).1, (hu₂ hx.2).2⟩

instance setoid (x : X) : Setoid (myPrestalk F x) where
  r := eventuallyEqual F x
  iseqv := by
    constructor
    intro s
    use ⟨s.1.1, s.1.2, le_of_inf_rfl⟩
    intro s t ⟨V, hV⟩
    use ⟨V, V.2.1, comm_of_le_of_inf V.2.2⟩
    exact hV.symm
    intro s t r ⟨U, hu⟩ ⟨V, hv⟩
    let W : {V // x ∈ V ∧ V ≤ s.1.1 ⊓ r.1.1} := ⟨U ⊓ V, mem_inf U.2.1 V.2.1, inf_le_inf_trans U.2.2 V.2.2⟩
    have h₁ : W.1 ≤ U.1 := myPresheaf.inf_le_left
    have h₂ : W.1 ≤ V.1 := myPresheaf.inf_le_right
    have : F.res (F.res s.sect (le_left_of_le_inf U.2.2)) h₁ = F.res (F.res r.sect (le_right_of_le_inf V.2.2)) h₂
    rw [hu, ← hv, myPresheaf.res_comp, myPresheaf.res_comp]
    use W
    rwa [myPresheaf.res_comp, myPresheaf.res_comp] at this

def myStalk (x : X) := @Quotient _ (setoid F x)

abbrev myPresheaf.stalk (x : X) := myStalk F x
abbrev myPresheaf.stalkMk {U : Opens X} (x : U) (s : F.sect U) : myStalk F x.val := ⟦⟨⟨U, x.2⟩, s⟩⟧

namespace myStalk

def StalkEq (x : X) {U V : OpenNhds x} (s : F.sect U.toOpens) (t : F.sect V.toOpens) := F.stalkMk ⟨x, U.2⟩ s = F.stalkMk ⟨x, V.2⟩ t

notation:50 a " ≡ " b " [STALK " F ", " x "]" => StalkEq F x a b

theorem stalkEq_def' (x : X) {U V : OpenNhds x} (s : F.sect U.toOpens) (t : F.sect V.toOpens) : (s ≡ t [STALK F, x]) ↔ F.stalkMk ⟨x, U.2⟩ s = F.stalkMk ⟨x, V.2⟩ t := Iff.rfl

theorem stalkEq_def (x : X) {U V : OpenNhds x} (s : F.sect U.toOpens) (t : F.sect V.toOpens) : (s ≡ t [STALK F, x]) ↔ eventuallyEqual F x ⟨U, s⟩ ⟨V, t⟩ := by
  rw [stalkEq_def', myPresheaf.stalkMk, myPresheaf.stalkMk, Quotient.eq, eventuallyEqual]
  rfl

theorem stalkEq_res (x : X) {U V : OpenNhds x} (huv : V.toOpens ≤ U.toOpens) (s : F.sect U.toOpens) : s ≡ F.res s huv [STALK F, x] := by
  rw [stalkEq_def]
  use ⟨V.toOpens, V.2, λ _ h ↦ ⟨huv h, h⟩⟩
  rw [myPresheaf.res_comp]

-- TODO: Merge the stalkEq api, and stalkMk api

theorem stalkMk_eq_stalkMk_iff (x : X) {U V : Opens X} (hu : x ∈ U) (hv : x ∈ V) (s : F.sect U) (t : F.sect V) : F.stalkMk ⟨x, hu⟩ s = F.stalkMk ⟨x, hv⟩ t ↔ eventuallyEqual F x ⟨⟨U, hu⟩, s⟩ ⟨⟨V, hv⟩, t⟩ := by rw [Quotient.eq]; rfl

theorem stalkMk_eq_res {U V : Opens X} (x : V) (huv : V ≤ U) (s : F.sect U) : F.stalkMk ⟨x, huv x.2⟩ s = F.stalkMk x (F.res s huv) := by
  rw [stalkMk_eq_stalkMk_iff]
  use ⟨V, x.2, λ _ h ↦ ⟨huv h, h⟩⟩
  rw [myPresheaf.res_comp]

end myStalk

def SheafificationObj (U : Opens X) := {f : (x : U) → F.stalk x.val // ∀ x : U, ∃ V : {V // x.val ∈ V ∧ V ≤ U}, ∃ σ : F.sect V.val, ∀v : V.val, F.stalkMk v σ = f ⟨v.1, V.2.2 v.2⟩}

open myPresheaf

def SheafificationHom {U V : Opens X} (huv : V ≤ U) (s : SheafificationObj F U) : SheafificationObj F V := ⟨λ x ↦  s.1 ⟨x, huv x.2⟩,
  by
    intro x
    let ⟨U_x, ⟨σ, hσ⟩⟩ := s.2 ⟨x, huv x.2⟩
    let V_x : {W // x.val ∈ W ∧ W ≤ V} := ⟨U_x.val ⊓ V, ⟨U_x.2.1, x.2⟩, λ _ h ↦ h.2⟩
    let σ' := F.res σ h₁
    use V_x, σ'
    intro v
    simp only
    rw [← myStalk.stalkMk_eq_res F v inf_le_left σ]
    exact hσ ⟨v, h₁ v.2⟩⟩

def mySheafification : myPresheaf X where
  obj := λ U ↦ SheafificationObj F U.unop
  map := λ m s ↦ SheafificationHom F (CategoryTheory.leOfHom m.unop) s

namespace mySheafification

instance sheafificationIsSheaf : IsSheaf (mySheafification F) where
  glueing' := sorry

end mySheafification
