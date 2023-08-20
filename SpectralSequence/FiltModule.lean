import SpectralSequence.Butterfly

import Mathlib.Algebra.Homology.ImageToKernel
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Homology
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.Algebra.Homology.HomologicalComplex

open Submodule CategoryTheory CategoryTheory.Category CategoryTheory.Limits Function LinearMap

theorem comp_eq_comp_left {C:Type _}[Category C]{X Y Z:C}{h: X⟶ Y}{f g: Y⟶ Z}(p: f=g):h≫f=h≫g:=by
  rw [p]

theorem comp_eq_comp_right {C:Type _}[Category C]{X Y Z:C}{f g: X⟶ Y}{h: Y⟶ Z}(p: f=g):f≫h=g≫h:=by
  rw [p]

noncomputable def homologyIso_lemma {C:Type _}[Category C][Abelian C]{X Y Z K H: C}(d1 : X ⟶ Y)(d2 : Y ⟶ Z)(w: d1≫ d2=0)(k: K ⟶ Y)(i : X ⟶ K)(h:K ⟶ H)(p1: d1 =i≫ k)(p2:Mono k)(p3:Exact k d2)(p4: Epi h)(p5: Exact i h) : homology d1 d2 w ≅ H := by
  apply Iso.trans
  apply homologyIsoCokernelLift
  let α := @CategoryTheory.asIso _ _ _ _ _ (Abelian.isIso_kernel_lift_of_exact_of_mono k d2 p3)
  have p6 : kernel.lift d2 d1 w = i ≫ α.1
  simp
  have p7 := CategoryTheory.Limits.kernel.lift_map d1 d2 w k d2 p3.w i (𝟙 Y) (𝟙 Z) (by simp; exact p1) (by simp)
  simp at p7
  rw [← p7]
  have p8 : kernel.map d2 d2 (𝟙 Y) (𝟙 Z) (by simp) = 𝟙 (kernel d2)
  unfold kernel.map
  simp
  have p9 := kernel.lift_ι d2 (kernel.ι d2) (by simp)
  have p10 : Mono (kernel.ι d2)
  unfold kernel.ι
  apply CategoryTheory.Limits.equalizer.ι_mono
  exact Mono.right_cancellation (kernel.lift d2 (kernel.ι d2) (by simp)) (𝟙 (kernel d2)) (by simp; exact p9)
  rw [p8]
  simp
  have p7 : Epi (α.2≫h)
  apply CategoryTheory.epi_comp
  have p8 : Exact (kernel.lift d2 d1 w) (α.2≫h)
  rw [p6]
  apply CategoryTheory.Preadditive.exact_of_iso_of_exact'
  pick_goal -2
  rfl
  pick_goal -2
  exact α
  pick_goal -2
  rfl
  pick_goal -2
  exact h
  pick_goal -2
  exact i
  simp
  rw [← Category.assoc,Iso.hom_inv_id]
  simp
  exact p5
  exact @CategoryTheory.asIso _ _ _ _ _ (Abelian.isIso_cokernel_desc_of_exact_of_epi (kernel.lift d2 d1 w) (α.inv ≫ h) p8)

variable (R:Type _) [Ring R]

theorem homology_SQ_range_ker (X Y Z:ModuleCat R)(d1:X⟶ Y)(d2:Y⟶ Z)(w:d1≫ d2=0): homology d1 d2 w ≅ SQ (range d1) (ker d2) := by
  let K : ModuleCat R := ker d2
  let H := SQ (range d1) (ker d2)
  let k : K ⟶ Y := by apply Submodule.subtype
  let i : X ⟶ K := by
    apply CategoryStruct.comp
    pick_goal 3
    exact ModuleCat.of R (range d1)
    apply LinearMap.rangeRestrict
    apply LinearMap.restrict
    swap
    apply LinearMap.id
    simp
    intro x
    rw [← LinearMap.comp_apply,← ModuleCat.comp_def,w]
    simp
  let h : K ⟶ H := by apply Submodule.mkQ
  have p1: d1 =i≫ k := by
    ext x
    simp
    rfl
  have p2: Mono k := by
    rw [ModuleCat.mono_iff_injective]
    apply injective_subtype
  have p3: Exact k d2 := by
    rw [ModuleCat.exact_iff,Submodule.range_subtype]
  have p4: Epi h := by
    rw [ModuleCat.epi_iff_surjective]
    apply mkQ_surjective
  have p5: Exact i h := by
    have : ∀x, i x = Subtype.mk (d1 x) (by simp;rw [← LinearMap.comp_apply,← ModuleCat.comp_def,w];simp) := by
      intro x
      rfl
    rw [ModuleCat.exact_iff,Submodule.ker_mkQ]
    ext x
    rw [mem_SQ_den,mem_range,mem_range]
    constructor
    intro p
    cases' p with y p
    rw [this] at p
    use y
    rw [← p]
    intro p
    cases' p with y p
    use y
    rw [this]
    congr
  exact homologyIso_lemma d1 d2 w k i h p1 p2 p3 p4 p5

structure FiltModuleCat extends ModuleCat R where
  filt : ℤ →o Submodule R carrier

def IsExhaustive (M: FiltModuleCat R) : Prop := ⨆ i : ℤ, M.filt i = ⊤

def IsBoundedbelow (M: FiltModuleCat R) : Prop := ∃ i : ℤ, M.filt i = ⊥

theorem iInf_of_Boundedbelow_filtmodule (M: FiltModuleCat R) (u: IsBoundedbelow R M) : ⨅ i : ℤ, M.filt i = ⊥ := by
  cases' u with i h
  rw [eq_bot_iff,← h]
  apply iInf_le

theorem Boundedbelow_imp_IsMinOn (M: FiltModuleCat R)(u: IsBoundedbelow R M): ∃ i0, IsMinOn M.filt univ i0 := by
  cases' u with i0 u
  use i0
  unfold IsMinOn
  unfold IsMinFilter
  simp
  intro x
  rw [u]
  simp

structure FiltLinearMap (M: FiltModuleCat R)  (M': FiltModuleCat R) extends M.carrier →ₗ[R] M'.carrier where
  map_filt : ∀ i: ℤ, map toLinearMap (M.filt i) ≤ M'.filt i

notation:25 M " →f[" R:25 "] " M':0 => FiltLinearMap R M M'

def FiltLinearMap.comp {M: FiltModuleCat R}{M':  FiltModuleCat R} {M'': FiltModuleCat R} (f : M →f[R] M') (g : M' →f[R] M'') : M →f[R] M'' where
  toLinearMap := g.1.comp f.1
  map_filt := by
    intro i
    rw [Submodule.map_comp]
    apply le_trans
    swap
    apply g.map_filt
    apply Submodule.map_mono
    apply f.map_filt

def FiltLinearMap.id (M: FiltModuleCat R) : M →f[R] M where
  toLinearMap := LinearMap.id
  map_filt := by simp

instance filtModuleCategory : Category (FiltModuleCat R) where
  Hom A B := A →f[R] B
  id A := FiltLinearMap.id R A
  comp f g := FiltLinearMap.comp R f g

theorem FiltLinearMap.comp_apply {M: FiltModuleCat R}{M':  FiltModuleCat R} {M'': FiltModuleCat R} (f : M ⟶ M') (g : M' ⟶ M'') : (f ≫ g).toLinearMap =LinearMap.comp g.toLinearMap f.toLinearMap := by
  rfl

theorem FiltLinearMap.id_apply (M: FiltModuleCat R) : (CategoryStruct.id M).toLinearMap  = LinearMap.id := by
  rfl

-- theorem filtModuleCat_iso (A B : FiltModuleCat R) (e : A ≅ B) (i: ℤ) : map e.1.toLinearMap (A.filt i) = (B.filt i)
-- := by
--   apply le_antisymm
--   apply FiltLinearMap.map_filt
--   intro x
--   simp
--   intro p
--   use e.2.toLinearMap x
--   constructor
--   apply e.2.map_filt
--   apply Set.mem_image_of_mem
--   exact p
--   rw [← LinearMap.comp_apply,← FiltLinearMap.comp_apply,e.inv_hom_id,FiltLinearMap.id_apply]
--   simp

instance FiltModule_zeroMorphism (A B: FiltModuleCat R) : Zero (A ⟶ B) where
  zero.toLinearMap := 0
  zero.map_filt := by simp

instance filModuleCatHasZero : HasZeroMorphisms (FiltModuleCat R) where
  comp_zero := by
    intro X Y f Z
    rfl
  zero_comp := by
    intro A B C f
    unfold filtModuleCategory
    simp
    unfold FiltLinearMap.comp
    congr
    apply LinearMap.comp_zero

theorem FiltLinearMap.zero_apply (M M': FiltModuleCat R) : (0 : M⟶ M').toLinearMap = 0 := by
  rfl

theorem comp_eq_zero_left {C:Type _}[Category C][HasZeroMorphisms C](X Y Z : C)(f:X ⟶ Y)(g:Y ⟶ Z)(p:f=0):f≫ g=0:=by
  rw [p]
  simp

theorem comp_eq_zero_right {C:Type _}[Category C][HasZeroMorphisms C](X Y Z : C)(f:X ⟶ Y)(g:Y ⟶ Z)(p:g=0):f≫ g=0:=by
  rw [p]
  simp

namespace filtModuleHomologoicalComplex

variable {R:Type _}[Ring R]{C: HomologicalComplex (FiltModuleCat R) (ComplexShape.down ℤ)}

def FC (p n: ℤ) : Submodule R (C.X n).carrier := (C.X n).filt p

def FK (p n: ℤ) : Submodule R (C.X n).carrier := comap (C.d n (n-1)).toLinearMap (FC p (n-1))

def FI (p n: ℤ) : Submodule R (C.X n).carrier := map (C.d (n+1) n).toLinearMap (FC p (n+1))

def Z (r p q: ℤ) : Submodule R (C.X (p+q)).carrier := (FC (p-1) (p+q)) + (FK (p-r) (p+q)) ⊓ (FC p (p+q))

def B (r p q: ℤ) : Submodule R (C.X (p+q)).carrier := (FC (p-1) (p+q)) + (FI (p+r-1) (p+q)) ⊓ (FC p (p+q))

def E (r p q: ℤ) :=
  SQ (@B R _ C r p q) (Z r p q)

theorem FC_mono (n : ℤ) : Monotone (fun p => @FC R _ C p n) := by
  intro a b p
  unfold FC
  dsimp
  apply (HomologicalComplex.X C n).filt.monotone'
  exact p

theorem FK_mono (n : ℤ) : Monotone (fun p => @FK R _ C p n) := by
  intro a b p
  unfold FK
  dsimp
  apply Submodule.comap_mono
  apply FC_mono
  exact p

theorem FI_mono (n : ℤ) : Monotone (fun p => @FI R _ C p n) := by
  intro a b p
  unfold FI
  dsimp
  apply Submodule.map_mono
  apply FC_mono
  exact p

theorem FI_eq_mapFC (p n : ℤ) : map (C.d n (n-1)).toLinearMap (@FC R _ C p n) = (@FI R _ C p (n-1)) := by
  unfold FI
  have : n-1+1=n
  simp
  rw [this]

theorem FK_eq_comapFC (p n : ℤ) : (@FK R _ C p n) = comap (C.d n (n-1)).toLinearMap (@FC R _ C p (n-1)):= by
  unfold FK
  rfl

theorem FI_le_FK (p1 p2 n : ℤ) : (@FI R _ C p1 n) ≤ (@FK R _ C p2 n) := by
  unfold FI FK
  rw [← Submodule.map_le_iff_le_comap,← Submodule.map_comp,← FiltLinearMap.comp_apply]
  simp
  rw [FiltLinearMap.zero_apply]
  simp

theorem Z_antitone (p q :ℤ) : Antitone (fun r => @Z R _ C r p q) := by
  intro a b h
  unfold Z
  dsimp
  apply left_add_right_inf_monotone
  apply FK_mono
  linarith

theorem B_mono (p q :ℤ) : Monotone (fun r => @B R _ C r p q) := by
  intro a b h
  unfold B
  dsimp
  apply left_add_right_inf_monotone
  apply FI_mono
  linarith

theorem B_le_Z (r1 r2 p q: ℤ) : (B r1 p q) ≤ (@Z R _ C r2 p q) := by
  unfold B
  unfold Z
  rw [Submodule.add_eq_sup,Submodule.add_eq_sup]
  apply left_add_right_inf_monotone
  apply FI_le_FK

noncomputable def SQZB_iso (r p q: ℤ) : SQ (@Z R _ C (r+1) p q) (Z r p q) ≅ SQ (@B R _ C r (p-r) (q+r-1)) (B (r+1) (p-r) (q+r-1)) :=
calc
  SQ (@Z R _ C (r+1) p q) (Z r p q) ≅  Butterfly (@FK R _ C (p - (r+1)) (p + q)) (FK (p - r) (p + q)) (FC (p-1) (p+q)) (FC p (p + q)) := by
    rfl
  _ ≅ Butterfly (@FC R _ C (p-1) (p+q)) (FC p (p + q)) (@FK R _ C (p - (r+1)) (p + q)) (FK (p - r) (p + q)) := by
    apply Butterfly_symm_iso
    apply FK_mono
    linarith
    apply FC_mono
    linarith
  _ ≅ (Butterfly (@FI R _ C (p-1) (p+q-1)) (FI p (p+q-1)) (FC (p-(r+1)) (p+q-1)) (FC (p-r) (p+q-1))) := by
    apply Butterfly_functorial_iso
    apply FC_mono
    linarith
    apply FK_mono
    linarith
    apply FC_mono
    linarith
    pick_goal -1
    exact (C.d (p+q) (p+q-1)).toLinearMap
    repeat rw [FI_eq_mapFC]
    repeat rw [FK_eq_comapFC]
  _ ≅ SQ (@B R _ C r (p-r) (q+r-1)) (B (r+1) (p-r) (q+r-1)) := by
    unfold Butterfly
    unfold B
    have num1 : p - (r + 1)= p - r - 1
    linarith
    have num2 : p - r + (q + r - 1) = p + q - 1
    linarith
    have num3 : p - r + r - 1 = p - 1
    linarith
    have num4 : p - r + (r + 1) - 1 = p
    linarith
    rw [num1,num2,num3,num4]

noncomputable def d (r p q: ℤ) : (@E R _ C r p q) ⟶ (@E R _ C r (p-r) (q+r-1)) := by
  apply CategoryStruct.comp
  apply SQ_id_hom
  exact B_le_Z r (r+1) p q
  rfl
  apply CategoryStruct.comp
  exact (SQZB_iso r p q).1
  apply SQ_id_hom
  rfl
  apply B_le_Z

theorem d_diff (r p q : ℤ): (@d R _ C r p q) ≫ (d r (p-r) (q+r-1)) = 0 := by
  unfold d
  simp
  apply comp_eq_zero_right
  apply comp_eq_zero_right
  rw [← Category.assoc]
  apply comp_eq_zero_left
  unfold SQ_id_hom
  rw [SQ_hom_comp]
  apply SQ_hom_zero
  simp
  rw [idmap]
  apply B_le_Z

noncomputable def homology_of_E (r p q: ℤ) : homology (@d R _ C r p q) (d r (p-r) (q+r-1)) (d_diff r p q) ≅ @E R _ C (r+1) (p-r) (q+r-1) := by
  let X := @E R _ C r p q
  let Y := @E R _ C r (p-r) (q+r-1)
  let K := SQ (@B R _ C r (p-r) (q+r-1)) (@Z R _ C (r+1) (p-r) (q+r-1))
  let H := @E R _ C (r+1) (p-r) (q+r-1)
  let d1:= @d R _ C r p q
  let d2:= @d R _ C r (p-r) (q+r-1)
  let w := @d_diff R _ C r p q
  let k : K ⟶ Y := by
    apply SQ_id_hom
    rfl
    apply Z_antitone
    linarith
  let i : X ⟶ K := by
    apply CategoryStruct.comp
    apply SQ_id_hom
    exact B_le_Z r (r+1) p q
    rfl
    apply CategoryStruct.comp
    exact (SQZB_iso r p q).1
    apply SQ_id_hom
    rfl
    apply B_le_Z
  let h : K ⟶ H := by
    apply SQ_id_hom
    apply B_mono
    linarith
    rfl
  have p1: d1 = i ≫ k := by
    simp
    unfold d
    repeat apply comp_eq_comp_left
    unfold SQ_id_hom
    rw [SQ_hom_comp]
  have p2: Mono k := by
    apply SQ_hom_mono
    apply B_le_Z
    rw [idcomap]
    simp
  have p3: Exact k d2 := by
    simp
    unfold d
    have o1: Mono (@SQZB_iso R _ C r (p - r) (q + r - 1)).hom
    apply IsIso.mono_of_iso
    have o2: Mono (SQ_id_hom (@B R _ C r (p - r - r) (q + r - 1 + r - 1)) (B (r + 1) (p - r - r) (q + r - 1 + r - 1)) (B r (p - r - r) (q + r - 1 + r - 1)) (Z r (p - r - r) (q + r - 1 + r - 1)))
    apply SQ_hom_mono
    apply B_mono
    linarith
    rw [idcomap]
    apply inf_le_left
    have o3: Mono ((@SQZB_iso R _ C r (p - r) (q + r - 1)).hom ≫ SQ_id_hom (B r (p - r - r) (q + r - 1 + r - 1)) (B (r + 1) (p - r - r) (q + r - 1 + r - 1)) (B r (p - r - r) (q + r - 1 + r - 1)) (Z r (p - r - r) (q + r - 1 + r - 1)))
    apply mono_comp
    apply exact_comp_mono
    apply SQ_ker_exact
    apply B_le_Z
    rw [idcomap]
    have : Z (r + 1) (p - r) (q + r - 1) ⊓ Z r (p - r) (q + r - 1) = @Z R _ C (r + 1) (p - r) (q + r - 1)
    rw [inf_eq_left]
    apply Z_antitone
    linarith
    rw [this,Submodule.add_eq_sup]
    symm
    rw [sup_eq_right]
    apply B_le_Z
  have p4: Epi h := by
    apply SQ_hom_epi
    rw [idmap]
    simp
  have p5: Exact i h := by
    simp
    have o1 : Epi (SQ_id_hom (@B R _ C r p q) (Z r p q) (Z (r + 1) p q) (Z r p q))
    apply SQ_hom_epi
    rw [idmap]
    simp
    have o2 : Epi (@SQZB_iso R _ C r p q).hom
    apply IsIso.epi_of_iso
    repeat apply exact_epi_comp
    apply SQ_cok_exact
    rw [idmap]
    simp
    apply B_mono
    linarith
  exact homologyIso_lemma d1 d2 w k i h p1 p2 p3 p4 p5

def FK_neginfty (n : ℤ) := ⨅ p : ℤ, @FK R _ C p n

def FI_infty (n : ℤ) := ⨆ p : ℤ, @FI R _ C p n

def Z_infty (p q : ℤ) := ⨅ r : ℤ, @Z R _ C r p q

def B_infty (p q : ℤ) := ⨆ r : ℤ, @B R _ C r p q

def E_infty (p q : ℤ) := SQ (@B_infty R _ C p q) (Z_infty p q)

theorem FK_neginfty_eq_ker (n : ℤ)(α : IsBoundedbelow R (C.X (n-1))) : FK_neginfty n = LinearMap.ker (C.d n (n-1)).toLinearMap := by
  unfold FK_neginfty
  unfold FK
  unfold FC
  unfold LinearMap.ker
  rw [← Submodule.comap_iInf]
  congr
  apply iInf_of_Boundedbelow_filtmodule
  assumption

theorem FI_infty_eq_range (n : ℤ)(β : IsExhaustive R (C.X (n+1))) : FI_infty n = LinearMap.range (C.d (n+1) n).toLinearMap := by
  unfold FI_infty
  unfold FI
  unfold FC
  unfold LinearMap.range
  rw [Submodule.copy_eq,← Submodule.map_iSup]
  congr

theorem Z_infty_eq (p q : ℤ)(α : IsBoundedbelow R (C.X (p+q-1))) : Z_infty p q = FC (p-1) (p+ q) + LinearMap.ker (C.d (p+q) (p+q-1)).toLinearMap ⊓ FC p (p+q) := by
  unfold Z_infty
  unfold Z
  rw [← FK_neginfty_eq_ker]
  unfold FK_neginfty
  rw [Submodule_exchange_limit2]
  simp
  have : ⨅ (i : ℤ), FK (p - i) (p + q) = ⨅ (p_1 : ℤ), @FK R _ C p_1 (p + q)
  apply Function.Surjective.iInf_congr
  pick_goal 3
  exact fun i => p-i
  intro q
  use p-q
  simp
  intro x
  rfl
  rw [this]
  cases' α with i0 α
  use p-i0
  unfold IsMinOn
  unfold IsMinFilter
  simp
  unfold FK
  unfold FC
  intro
  apply Submodule.comap_mono
  rw [α]
  simp
  assumption

theorem B_infty_eq (p q : ℤ)(β : IsExhaustive R (C.X (p+q+1))): B_infty p q = FC (p-1) (p+ q) + LinearMap.range (C.d (p+q+1) (p+q)).toLinearMap ⊓ FC p (p+q) := by
  unfold B_infty
  unfold B
  rw [← FI_infty_eq_range]
  unfold FI_infty
  rw [Submodule_exchange_limit1]
  have : (⨆ (i : ℤ), FI (p + i - 1) (p + q))= (⨆ (p_1 : ℤ), @FI R _ C p_1 (p + q))
  apply Function.Surjective.iSup_congr
  pick_goal 3
  exact fun x=> p+x-1
  intro a
  use - p + a +1
  simp
  linarith
  intro x
  rfl
  rw [this]
  apply directed_of_sup
  intro a b p
  apply FI_mono
  linarith
  assumption

def FH (p q :ℤ) := LinearMap.range (C.d (q+1) q).toLinearMap + (FC p q) ⊓ LinearMap.ker (C.d q (q-1)).toLinearMap

theorem FH_exhaustive (n: ℤ)(u: IsExhaustive R (C.X n)) : ⨆ p, @FH R _ C p n = LinearMap.ker (C.d n (n-1)).toLinearMap := by
  unfold FH
  unfold FC
  rw [Submodule_exchange_limit1,u]
  simp
  rw [LinearMap.range_le_ker_iff,← FiltLinearMap.comp_apply]
  simp
  rw [FiltLinearMap.zero_apply]
  apply directed_of_sup
  intro a b p
  apply (HomologicalComplex.X C n).filt.monotone'
  linarith

theorem FH_boundedebelow (n: ℤ) (u: IsBoundedbelow R (C.X n)) : ∃ p, @FH R _ C p n = LinearMap.range (C.d (n+1) n).toLinearMap := by
  cases' u with i0 u
  use i0
  unfold FH
  unfold FC
  rw [u]
  simp

noncomputable def E_infty_iso (p q : ℤ)(α : IsBoundedbelow R (C.X (p+q-1)))(β : IsExhaustive R (C.X (p+q+1))) : @E_infty R _ C p q ≅ SQ (@FH R _ C (p-1) (p+q)) (FH p (p+q)) := by
  unfold E_infty
  rw [Z_infty_eq,B_infty_eq]
  unfold FH
  apply Butterfly_symm_iso
  rw [LinearMap.range_le_ker_iff,← FiltLinearMap.comp_apply]
  simp
  rw [FiltLinearMap.zero_apply]
  apply FC_mono
  linarith
  repeat assumption

theorem E_zero_iso (p q : ℤ) : @E R _ C 0 p q ≅ SQ (@FC R _ C (p-1) (p+q)) (FC p (p+q)) := by
  unfold E
  unfold B
  unfold Z
  apply CategoryTheory.Iso.trans
  apply Butterfly_symm_iso
  apply FI_le_FK
  apply FC_mono
  linarith
  unfold Butterfly
  simp
  have a : @FC R _ C p (p+q) ≤ FK p (p+q)
  unfold FC
  unfold FK
  rw [← map_le_iff_le_comap]
  apply (HomologicalComplex.d C (p + q) (p + q - 1)).map_filt
  have b : @FI R _ C (p-1) (p+q) ≤ FC (p-1) (p+q)
  unfold FI
  unfold FC
  apply (HomologicalComplex.d C (p + q +1) (p + q )).map_filt
  have c: FI (p - 1) (p + q) ⊔ FC (p - 1) (p + q) ⊓ FK p (p + q) = @FC R _ C (p-1) (p+q)
  have : FC (p - 1) (p + q) ⊓ FK p (p + q) = @FC R _ C (p-1) (p+q)
  simp
  apply le_trans
  swap
  exact a
  apply FC_mono
  linarith
  rw [this]
  simp
  exact b
  have dl: FI (p - 1) (p + q) ⊔ FC p (p + q) ⊓ FK p (p + q) =@FC R _ C p (p+q)
  have : FC p (p + q) ⊓ FK p (p + q) =@FC R _ C p (p+q)
  simp
  exact a
  rw [this]
  simp
  apply le_trans
  exact b
  apply FC_mono
  linarith
  rw [c,dl]

end filtModuleHomologoicalComplex
