import Mathlib
open Ring Ideal Set Topology TopologicalSpace

structure mySpec (A : Type*) [CommRing A] where
  ideal : Ideal A
  isPrime : ideal.IsPrime

namespace mySpec

instance (A : Type*) [CommRing A] : Coe (mySpec A) (Ideal A) := ⟨mySpec.ideal⟩

def V : {A : Type*} → [CommRing A] → Ideal A → Set (mySpec A) := λ I ↦ {p | I ≤ p.ideal}
def V' : {A : Type*} → [CommRing A] → Set A → Set (mySpec A) := λ S ↦ {p | S ⊆ p.ideal}
def D : {A : Type*} → [CommRing A] → A → Set (mySpec A) := λ r ↦ {p | r ∉ p.ideal}

variable {A : Type*} [CommRing A]
theorem lemma_2_1_a (α β : Ideal A) : V (α*β) = (V α) ∪ (V β) := by
  ext p
  constructor; intro hp
  by_cases hp₁ : β ≤ p
  right; exact hp₁
  left
  let ⟨b, hb⟩ := Set.not_subset.mp hp₁
  intro a ha
  have : a * b ∈ p.ideal := hp (Ideal.mul_mem_mul ha hb.1)
  have := (Ideal.isPrime_iff.mp p.2).2 this
  exact this.resolve_right hb.2
  rintro (hp | hp)
  have := mul_top p.ideal ▸ Ideal.mul_mono hp (λ _ _ ↦ trivial : β ≤ ⊤)
  exact this
  have : α ≤ ⊤ := λ _ _ ↦ trivial
  have := top_mul p.ideal ▸ Ideal.mul_mono this hp
  exact this

theorem lemma_2_1_b {ι : Type*} (α : ι → Ideal A) : V (⨆ i, α i) = ⋂ i, V (α i) := by
  ext p
  simp_rw [V, iSup_le_iff, mem_iInter]
  exact Iff.rfl

theorem lemma_2_1_b' (S : Set (Ideal A)) : V (sSup S) = ⋂₀ (V '' S) := by
  ext p
  simp_rw [V, sSup_le_iff, mem_sInter, mem_setOf, mem_image]
  constructor <;> intro hp
  intro T ⟨x, hx⟩
  rw [← hx.2, mem_setOf]
  exact hp x hx.1
  intro b hb
  let U := V b
  exact hp U ⟨b, hb, rfl⟩

lemma hehe (α : Ideal A) : V α = V α.radical := by
  ext p
  constructor <;> intro hp
  simp_rw [V] at *
  rw [radical_eq_sInf, mem_setOf]
  exact sInf_le ⟨hp, p.2⟩
  exact λ _ h ↦ hp (le_radical h)

theorem V'_eq_V_of_span (S : Set A) : V' S = V (span S) := by
  ext p; constructor <;> intro hp
  rw [V, V', mem_setOf] at *
  exact span_le.mpr hp
  intro x hx
  rw [V, mem_setOf] at hp
  exact hp (subset_span hx)

theorem V'_eq_V_comp_span : (V' : Set A → Set (mySpec A)) = V ∘ span := by
  funext s
  rw [V'_eq_V_of_span]
  rfl

theorem lemma_2_1_c {α β : Ideal A} : V α ⊆ V β ↔ β.radical ≤ α.radical := by
  constructor <;> intro h
  simp_rw [Ideal.radical_eq_sInf]
  apply le_sInf
  have : {J | α ≤ J ∧ J.IsPrime} ⊆ {J | β ≤ J ∧ J.IsPrime}
  intro p hp
  let p' : mySpec A := ⟨p, hp.2⟩
  have : p' ∈ V α := hp.1
  exact ⟨h this, hp.2⟩
  intro b hb
  exact sInf_le (this hb)
  rw [hehe α, hehe β]
  exact λ _ hp _ hx ↦ hp (h hx)

theorem aux1 : ∅ ∈ range (@V A _) := by
  use ⊤
  rw [eq_empty_iff_forall_not_mem]
  intro p
  rw [V, mem_setOf, top_le_iff]
  exact p.2.ne_top

theorem aux2 : ∀ (S : Set (Set (mySpec A))), S ⊆ range V → ⋂₀ S ∈ range V := by
  intro S hS
  let ⟨U, hU⟩ := subset_range_iff_exists_image_eq.mp hS
  have := lemma_2_1_b' U
  rw [← hU, ← this]
  exact mem_range_self (sSup U)

theorem aux3 : ∀ S ∈ range V, ∀ U ∈ range V, S ∪ U ∈ range (@V A _) := by
  intro S ⟨S', hS'⟩ U ⟨U', hU'⟩
  rw [← hU', ← hS', ← lemma_2_1_a]
  exact mem_range_self (S' * U')

instance zariskiTop : TopologicalSpace (mySpec A) := ofClosed (range V) aux1 aux2 aux3

example {I : Ideal A} : IsClosed (V I) := by
  rw [← @isOpen_compl_iff]
  have : ((V I)ᶜ)ᶜ ∈ range V
  rw [compl_compl]
  use I
  exact this

theorem isOpen_iff {Y : Set (mySpec A)} : IsOpen Y ↔ ∃I, (V I)ᶜ = Y := ⟨λ ⟨I, hI⟩ ↦ ⟨I, (eq_compl_comm.mp hI).symm⟩, λ ⟨I, hI⟩ ↦ ⟨I, eq_compl_comm.mp hI.symm⟩⟩

theorem isClosed_iff {Y : Set (mySpec A)} : IsClosed Y ↔ ∃I, V I = Y := by simp_rw [← isOpen_compl_iff, isOpen_iff, compl_inj_iff]

theorem isOpen_of_hypersurface (f : A) : IsOpen (D f) := by
  rw [isOpen_iff]
  use span {f}
  ext p
  rw [← V'_eq_V_of_span, V', D, mem_compl_iff, mem_setOf, mem_setOf, singleton_subset_iff]
  rfl

theorem hypersurface_of_mul_eq_inter (f g : A) : D (f*g) = D f ∩ D g := by
  ext p; constructor <;> intro h
  rw [mem_inter_iff, D, D, mem_setOf, mem_setOf] at *
  by_contra h₁
  push_neg at h₁
  by_cases hf : f ∈ p.ideal
  have : f*g ∈ p.ideal := mul_mem_right g p.ideal hf
  exact h this
  have : f*g ∈ p.ideal := mul_mem_left p.ideal f (h₁ hf)
  exact h this
  contrapose h
  rw [mem_inter_iff, D, D, mem_setOf, mem_setOf] at *
  have h : f * g ∈ p.ideal := by tauto
  have := p.2.mem_or_mem h
  tauto

theorem iUnion_of_hypersurfaces_eq {ι : Type*} (f : ι → A) : ⋃ i, D (f i) = (V (span (range f)))ᶜ := by
  ext p
  simp_rw [mem_iUnion, D, mem_setOf, ← V'_eq_V_of_span, V', mem_compl_iff, mem_setOf, not_subset_iff_exists_mem_not_mem]
  constructor
  intro ⟨i, hi⟩
  use f i
  constructor
  use i
  exact hi
  intro ⟨x, hx⟩
  let ⟨i, hi⟩ := hx.1
  use i
  rw [hi]
  exact hx.2

theorem eq_iUnion_of_hypersurfaces_if_isOpen {U : Set (mySpec A)} {I} (hU : U = (V I)ᶜ) : ⋃ i : I, D i.val = U := by
  ext p
  have : (range (Subtype.val : I → A)) = I
  ext f
  constructor
  intro ⟨i, hi⟩
  rw [← hi]
  exact i.2
  intro hf
  use ⟨f, hf⟩
  rw [iUnion_of_hypersurfaces_eq, hU, mem_compl_iff, V, V, mem_setOf, mem_compl_iff, mem_setOf, this, span_eq]

theorem eq_sUnion_of_hypersurfaces_if_isOpen {U : Set (mySpec A)} {I} (hU : U = (V I)ᶜ) : ⋃₀ {D f | f ∈ I} = U := by
  have : ⋃ i : I, D i.val = ⋃₀ {D f | f ∈ I}
  ext p
  constructor <;> intro ⟨t, ht⟩ <;> let ⟨i, hi⟩ := ht.1
  simp_rw [mem_sUnion, mem_setOf]
  use t
  constructor
  use i.val
  constructor
  exact i.2
  exact hi
  exact ht.2
  rw [mem_iUnion]
  use ⟨i, hi.1⟩
  rw [hi.2]
  exact ht.2
  rw [← this]
  exact eq_iUnion_of_hypersurfaces_if_isOpen hU

theorem hypersurface_isBasis : IsTopologicalBasis {D f | f : A} where
  exists_subset_inter := by
    intro t₁ ⟨f₁, hf₁⟩ t₂ ⟨f₂, hf₂⟩ x hx
    use D (f₁*f₂)
    constructor
    use f₁*f₂
    constructor
    rwa [hypersurface_of_mul_eq_inter, hf₁, hf₂]
    rw [hypersurface_of_mul_eq_inter, hf₁, hf₂]
  sUnion_eq := by
    ext p; constructor <;> intro _
    trivial
    have := (ne_top_iff_one p.ideal).mp p.2.1
    rw [mem_sUnion]
    use D 1
    constructor; use 1
    exact this
  eq_generateFrom := by
    ext x; constructor <;> intro hx
    rw [isOpen_iff] at hx
    let ⟨I, hI⟩ := hx
    rw [isOpen_mk]
    have h₁ := eq_sUnion_of_hypersurfaces_if_isOpen hI.symm
    rw [← h₁]
    apply GenerateOpen.sUnion
    intro s ⟨f, hf⟩
    rw [← hf.2]
    apply GenerateOpen.basic
    use f
    induction' hx with s hs s t _ _ hs ht S _ hS
    let ⟨f, hf⟩ := hs
    rw [← hf]
    exact isOpen_of_hypersurface f
    exact isOpen_univ
    exact IsOpen.inter hs ht
    exact isOpen_sUnion hS

variable {R₁ R₂ R₃ : Type*} [CommRing R₁] [CommRing R₂] [CommRing R₃]

def functMap (φ : R₁ →+* R₂) : mySpec R₂ → mySpec R₁ := λ p' ↦ ⟨p'.ideal.comap φ, Ideal.comap_isPrime φ (H := p'.2)⟩

theorem functMap_preimage_of_hypersurface (φ : R₁ →+* R₂) (f : R₁) : functMap φ ⁻¹' (D f) = D (φ f) := rfl

theorem continuous_if_continuous_on_base {X Y : Type*} [TopologicalSpace X] [inst : TopologicalSpace Y] {S : Set (Set Y)} (hS : IsTopologicalBasis S) {f : X → Y} (hf : ∀s ∈ S, IsOpen (f ⁻¹' s)) : Continuous f := by
  constructor
  intro U hU
  rw [IsTopologicalBasis.isOpen_iff hS] at hU
  choose g h₁ h₂ h₃ using hU
  have : U = ⋃ u : U, g u.1 u.2
  ext y; constructor <;> intro hy
  rw [mem_iUnion]
  use ⟨y, hy⟩
  exact h₂ y hy
  rw [mem_iUnion] at hy
  let ⟨u, hu⟩ := hy
  exact (h₃ u.1 u.2) hu
  rw [this, Set.preimage_iUnion]
  apply isOpen_iUnion
  exact λ u ↦ hf _ (h₁ u.1 u.2)

theorem isContinuous_functMap (φ : R₁ →+* R₂) : Continuous (functMap φ) := by
  apply continuous_if_continuous_on_base hypersurface_isBasis
  intro s ⟨f, hf⟩
  rw [← hf, functMap_preimage_of_hypersurface]
  exact isOpen_of_hypersurface (φ f)

theorem functMap_comp (φ₁ : R₁ →+* R₂) (φ₂ : R₂ →+* R₃) : functMap (φ₂.comp φ₁) = (functMap φ₁) ∘ (functMap φ₂) := rfl

open CategoryTheory

def SpecFunctTop : CommRingCatᵒᵖ ⥤ TopCat where
  obj := λ ⟨R⟩ ↦ ⟨@mySpec R.1 R.2, zariskiTop⟩
  map := λ ⟨φ⟩ ↦ ⟨functMap φ, isContinuous_functMap φ⟩
