import Mathlib
import MyProject.mySheafTheory

variable {X : TopCat} {Y : X → RingCat} (p : (U : Opens X) → ((x : U) → Y x) → Prop) [inst : ∀U, Ring {f | p U f}]

def restrict {U V : Set X} (f : (x : U) → Y x) (huv : V ⊆ U) : (x : V) → Y x := λ ⟨v, hv⟩ ↦ f ⟨v, huv hv⟩

variable (hp : ∀ (U V : Opens X) (f : (x : U) → Y x), (huv : V ≤ U) → p U f → p V (restrict f huv))

-- def functionPresheaf_restrict_map {U V : Opens X} (huv : V ≤ U) : RingCat.of {f | p U f} ⟶ RingCat.of {f | p V f} where
--   toFun := λ f : {f | p U f} ↦ ⟨restrict f.1 huv, hp U V f huv f.2⟩
--   map_one' := sorry


-- def functionPresheaf : myPresheaf X where

-- structure OpenNhdsIn (x : X) (U : Set X) where
--   carrier : Set X
--   isOpen : IsOpen carrier
--   mem : x ∈ carrier
--   subset : carrier ⊆ U

-- def OpenNhdsIn.toOpens {x : X} {U : Set X} (s : OpenNhdsIn x U) : Opens X where
--   carrier := s.carrier
--   isOpen := s.isOpen

-- def localized : (U : Set X) → ((x : U) → Y x) → Prop := λ U f ↦ ∀x ∈ U, ∃S : OpenNhdsIn x U, p S.toOpens (restrict f S.subset)

-- abbrev bundledMaps (U : Set X) : Type _ := ↥{f | (localized p) U f}

-- def restrictMap {U V : Opens X} (f : bundledMaps p U) (huv : V ≤ U): bundledMaps p V where
--   val := restrict f.1 huv
--   property := by
--     rw [Set.mem_setOf]
--     intro x hx
--     let ⟨S₁, hS₁⟩ := f.2 x (huv hx)
--     let S₂ : OpenNhdsIn x V := ⟨S₁.carrier ∩ V.carrier, sorry, sorry, sorry⟩
--     use S₂
--     apply hp



-- variable (inst : ∀ U, Ring (bundledMaps p U))

-- instance {U : Set X} : Ring (bundledMaps p U) := inst U

-- def restrictHom {U V : Set X} (huv : V ⊆ U) : RingCat.of (bundledMaps p U) ⟶ RingCat.of (bundledMaps p V) where
--   toFun := λ (f : bundledMaps p U) ↦ ⟨restrict f huv, sorry⟩
