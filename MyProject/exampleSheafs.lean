import Mathlib
import MyProject.mySheafTheory

open CategoryTheory Topology ContinuousMap Opposite myPresheaf

variable (X Y : Type*) [TopologicalSpace X] [Ring Y]

def restrict {U V : Set X} (f : U → Y) (huv : V ⊆ U) : V → Y := λ ⟨v, hv⟩ ↦ f ⟨v, huv hv⟩

def restrictHom {U V : Set X} (huv : V ⊆ U) : RingCat.of (U → Y) ⟶ RingCat.of (V → Y) where
  toFun := λ f ↦ restrict X Y f huv
  map_one' := rfl
  map_mul' := λ _ _ ↦ rfl
  map_zero' := rfl
  map_add' := λ _ _ ↦ rfl

def 𝒪 : myPresheaf X where
  obj := λ U ↦ RingCat.of (U.unop.carrier → Y)
  map := λ m ↦ restrictHom X Y (leOfHom m.unop)

theorem mem_iSup {ι : Type u_3} {U : ι → Opens X} : ∀x ∈ ⨆ i, U i, ∃j, x ∈ U j := by
    intro x ⟨t, ht⟩
    let ⟨j, hj⟩ := ht.1
    let ⟨k, hk⟩ := hj.1
    use k
    simp only at hk
    rw [hk]
    have : x ∈ j.carrier
    rw [hj.2]; exact ht.2
    exact this

noncomputable def g {ι : Type u_3} {U : ι → Opens X} (x : ↥(⨆ i, U i)) : ι := Classical.choose (mem_iSup X x.1 x.2)

theorem h₁ {ι : Type u_3} {U : ι → Opens X} (x : X) (hx : x ∈ ⨆ i, U i) : x ∈ U (g X ⟨x, hx⟩) := Classical.choose_spec (mem_iSup X x hx)

noncomputable def glue {ι : Type u_3} {U : ι → Opens X} (s : (i : ι) → ↑((𝒪 X Y).sect (U i))) : (𝒪 X Y).sect (⨆ j, U j) := λ x : (⨆ i, U i).carrier ↦ s (g X x) ⟨x.1, h₁ X x.1 x.2⟩

theorem this {ι : Type u_3} {U : ι → Opens X} (s : (i : ι) → ↑((𝒪 X Y).sect (U i))) : ∀ x : (⨆ i, U i).carrier, ∃ i, ∃ y : U i, y.1 = x.1 ∧ glue X Y s x = s i y := λ x ↦ ⟨g X x, ⟨x.1, h₁ X x.1 x.2⟩, rfl, rfl⟩

theorem res_eq {U V : Opens X} (f : (𝒪 X Y).sect U) (g : (𝒪 X Y).sect V) (huv : V ≤ U) : res f huv = g ↔ ∀x : V, f ⟨x.1, huv x.2⟩ = g x := by
  constructor <;> intro hfg
  intro x
  rw [← hfg]
  rfl
  funext x
  rw [← hfg x]
  rfl

theorem eq_res {U V : Opens X} (f : (𝒪 X Y).sect U) (g : (𝒪 X Y).sect V) (huv : V ≤ U) : g = res f huv ↔ ∀x : V, g x = f ⟨x.1, huv x.2⟩  := by
  rw [Eq.comm]
  simp_rw [Eq.comm (a := g _)]
  exact res_eq X Y f g huv

theorem res_eq_res {U V W : Opens X} (huw : W ≤ U) (hvw : W ≤ V) (f : (𝒪 X Y).sect U) (g : (𝒪 X Y).sect V) : res f huw = res g hvw ↔ ∀x : W, f ⟨x.1, huw x.2⟩ = g ⟨x.1, hvw x.2⟩ := by
  constructor <;> intro h
  intro w
  rw [res_eq] at h
  have := h w
  rw [this]
  rfl
  rw [res_eq]
  intro w
  have := h w
  rw [this]
  rfl

theorem eq_of_subdomain {U V : Opens X} (huv : V ≤ U) (f : (𝒪 X Y).sect U) (x : V) : res f huv x = f ⟨x.1, huv x.2⟩ := rfl

instance : IsSheaf (𝒪 X Y) where
  glueing' := by
    intro ι U s hs
    use glue X Y s
    constructor
    intro i
    rw [res_eq]
    intro x
    let ⟨j, y, hj, hy⟩ := this X Y s ⟨x.1, myPresheaf.le_iSup i x.2⟩
    rw [hy]
    simp_rw [Compatible, res_eq_res] at hs
    let z : ↥(U j ⊓ U i) := ⟨x.1, hj.symm ▸ y.2, x.2⟩
    have : y = ⟨z.1, inf_le_left z.2⟩ := Subtype.ext hj
    have h₁ := eq_of_subdomain X Y inf_le_left (s j) z
    rw [← this] at h₁
    rw [← h₁]
    have : x = ⟨z.1, inf_le_right z.2⟩ := rfl
    have h₂ := eq_of_subdomain X Y inf_le_right (s i) z
    rw [← this] at h₂
    rw [← h₂]
    exact hs j i z
    intro f' hf'
    funext (x : ↥(⨆ j, U j))
    let ⟨i, y, hy⟩ := this X Y s x
    simp_rw [res_eq] at hf'
    have := hf' i y
    have hy' : ⟨y.1, le_iSup i y.2⟩ = x := Subtype.ext hy.1
    rw [← hy', hf', ← hy.2, hy']

