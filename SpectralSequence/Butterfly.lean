import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Basic
import Mathlib.Deprecated.Subgroup
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.Span
import Mathlib.LinearAlgebra.Quotient
import Mathlib.Order.Directed
import Mathlib.Algebra.Module.Equiv
import Mathlib.Algebra.Homology.ImageToKernel
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Homology
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Balanced

open Set Function Submodule CategoryTheory

section

variable {C:Type _}[Category C][Abelian C]{X Y Z W: C}{f: X ⟶ Y}{g: Y ⟶ Z}{h: Z ⟶ W}(p:Exact f g)(q:Exact g h)

theorem mono_of_exact (q:Limits.IsZero X) : Mono g := by
  rw [mono_iff_exact_zero_left]
  have h : X ≅ @OfNat.ofNat C 0 (@Zero.toOfNat0 C (Limits.HasZeroObject.zero' C))
  apply Limits.IsZero.iso
  assumption
  apply Limits.isZero_zero
  apply CategoryTheory.Preadditive.exact_of_iso_of_exact' f g 0 g
  repeat pick_goal -1; rfl
  pick_goal -1
  assumption
  simp
  symm
  apply Limits.zero_of_source_iso_zero
  assumption
  simp
  assumption

theorem epi_of_exact (q:Limits.IsZero W) : Epi g := by
  rw [epi_iff_exact_zero_right]
  have o : W ≅ @OfNat.ofNat C 0 (@Zero.toOfNat0 C (Limits.HasZeroObject.zero' C))
  apply Limits.IsZero.iso
  assumption
  apply Limits.isZero_zero
  apply CategoryTheory.Preadditive.exact_of_iso_of_exact' g h g 0
  pick_goal -1
  assumption
  repeat pick_goal -1; rfl
  simp
  simp
  have : h = 0
  apply Limits.zero_of_target_iso_zero
  assumption
  rw [this]
  simp
  assumption

noncomputable def iso_of_exact (a:Limits.IsZero X)(b:Limits.IsZero W) : Y ≅ Z:= by
  have isog : IsIso g := by
    rw [isIso_iff_mono_and_epi]
    constructor
    apply mono_of_exact
    repeat assumption
    apply epi_of_exact
    repeat assumption
  exact @CategoryTheory.asIso _ _ _ _ _ isog

end

section

variable {X:Type _}[Lattice X][IsModularLattice X](A B C D: X)(v:A ≤ B)(w:C ≤ D)

theorem Lattice_lemma1 : (B ⊓ D) ⊓ (C ⊔ A ⊓ D)=B ⊓ C ⊔ A ⊓ D := by
  conv => left; rw [inf_assoc]; right ;rw [inf_comm,sup_comm]
  rw [sup_inf_assoc_of_le]
  swap
  apply inf_le_right
  rw [inf_comm,sup_inf_assoc_of_le]
  swap
  apply le_trans
  apply inf_le_left
  assumption
  rw [sup_comm,inf_comm]
  congr
  rw [inf_eq_left]
  assumption

theorem Lattice_lemma2 : (B ⊓ D) ⊔ (C ⊔ A ⊓ D)= C ⊔ B ⊓ D := by
  rw [sup_comm, sup_assoc]
  congr
  simp
  apply le_trans
  apply inf_le_left
  assumption

end

variable {R :Type _}[Ring R]{X X' X'': ModuleCat R}{f : X ⟶ X'}{g: X'⟶ X''}{A B C D : Submodule R X}(N H :Submodule R X){A' B' C' D': Submodule R X'}{A'' B'': Submodule R X''}{I:Type _}[Nonempty I](F:I → Submodule R X)(fA : map f A ≤ A')(fB : map f B ≤ B')(fC : map f C ≤ C')(fD : map f D ≤ D')(gA: map g A' ≤ A'')(gB: map g B' ≤ B'')

theorem left_add_right_inf_monotone (p: A≤B): C+A⊓D≤ C+B⊓ D:= by
  repeat rw [Submodule.add_eq_sup]
  apply sup_le_sup_left
  apply inf_le_inf_right
  assumption

theorem comap_map_lemma1 (A :Submodule R X) (C' :Submodule R X') : comap f (C' + map f A) = comap f C' + A := by
  ext x
  simp
  rw [mem_sup,mem_sup]
  simp
  constructor
  rintro ⟨y,p1,z,p2,p3⟩
  use (x-z)
  simp
  rw [← p3]
  simp
  constructor
  assumption
  use z
  simp
  assumption
  rintro ⟨y,p1,z,p2,p3⟩
  use f y
  constructor
  assumption
  use z
  constructor
  assumption
  rw [← p3]
  simp

theorem comap_map_lemma2 (B:Submodule R X)(D': Submodule R X'): map f (B ⊓ comap f D') = map f B ⊓ D' := by
  ext x
  simp
  constructor
  rintro ⟨y,p1,p2⟩
  constructor
  use y
  tauto
  rw [← p2]
  exact p1.2
  intro p
  cases' p with p1 p2
  cases' p1 with y p1
  cases' p1 with p1 p3
  use y
  rw [← p3] at p2
  tauto

-- Submodule Quotient
def SQ_den (A B:Submodule R X): Submodule R B := by
  repeat constructor; swap
  exact {x | Subtype.val x ∈ A }
  simp
  intro a _ b _
  apply AddSubsemigroup.add_mem'
  simp
  simp
  intro r a _
  apply smul_mem

def mem_SQ_den (A B:Submodule R X)(x:B):x∈ SQ_den A B ↔ x.val ∈ A:= by
  rfl

def SQ (A B:Submodule R X) : ModuleCat R := ModuleCat.mk (B⧸SQ_den A B)

theorem SQ_zero (A B :Submodule R X)(p: B ≤ A): Limits.IsZero (SQ A B) := by
  apply @ModuleCat.isZero_of_subsingleton R _ (SQ A B) (by
    apply subsingleton_quotient_iff_eq_top.mpr
    ext x
    rw [mem_SQ_den]
    simp
    apply p
    simp)

def SQ_map : SQ A B → SQ A' B' := by
  apply Quot.lift
  swap
  intro x
  apply Quot.mk
  apply Subtype.mk
  swap
  exact f x.val
  apply fB
  apply Set.mem_image_of_mem
  simp
  intro a b p
  cases' a with a pa
  cases' b with b pb
  rw [quotientRel_r_def] at p
  rw [Quot.eq]
  apply EqvGen.rel
  rw [quotientRel_r_def,mem_SQ_den]
  rw [mem_SQ_den] at p
  have p : a-b ∈ A
  exact p
  apply fA
  have h1 : f (a - b) ∈ @image ↑X ↑X' ↑f ↑A
  apply Set.mem_image_of_mem
  exact p
  conv at h1 => lhs; simp
  exact h1

theorem SQ_map_apply (x: B) : SQ_map fA fB (Quot.mk _ x) = Quot.mk _ (Subtype.mk (f x) (by apply fB; apply mem_image_of_mem; simp)) := by
  unfold SQ_map
  rfl

theorem subtype_hom_add (x y:A): (Subtype.mk (f (x+y).val) (by apply fA; apply mem_image_of_mem; simp; apply AddSubsemigroup.add_mem';simp;simp) : ModuleCat.of R A') = Subtype.mk (f x.val) (by apply fA; apply mem_image_of_mem; simp) + Subtype.mk (f y.val) (by apply fA; apply mem_image_of_mem; simp):= by
  simp

theorem subtype_hom_smul (r:R)(x:A): (Subtype.mk (f (r•x).val) (by apply fA; apply mem_image_of_mem; simp; apply Submodule.smul_mem';simp) : ModuleCat.of R A') = r • Subtype.mk (f x.val) (by apply fA; apply mem_image_of_mem; simp) := by
  simp

def SQ_hom : SQ A B ⟶ SQ A' B' := by
  repeat constructor; swap
  apply SQ_map fA fB
  apply Quotient.ind₂
  unfold Quotient.mk
  intro a b
  have p1 : @HAdd.hAdd (↑(SQ A B)) (↑(SQ A B)) (↑(SQ A B)) instHAdd (Quot.mk (@Setoid.r (↑(ModuleCat.of R { x // x ∈ B })) (quotientRel (SQ_den A B))) a) (Quot.mk _ b) = Quot.mk _ (a+b)
  congr
  rw [p1,SQ_map_apply,SQ_map_apply,SQ_map_apply,subtype_hom_add]
  congr
  intro r
  apply Quot.ind
  intro a
  have p1 : @HSMul.hSMul R (↑(SQ A B)) (↑(SQ A B)) instHSMul r (Quot.mk _ a) = Quot.mk _ (r•a)
  congr
  simp
  rw [← Submodule.Quotient.quot_mk_eq_mk,p1,SQ_map_apply,SQ_map_apply,subtype_hom_smul]
  congr

theorem SQ_hom_apply (x: B) : SQ_hom fA fB (Quot.mk _ x) =  Quot.mk _ (Subtype.mk (f x) (by apply fB; apply mem_image_of_mem; simp)) := by
  apply SQ_map_apply
  exact fA

theorem map_lemma : map (f ≫ g) A ≤ A'' := by
  rw [ModuleCat.comp_def,Submodule.map_comp]
  apply le_trans
  swap
  exact gA
  apply map_mono
  exact fA

theorem SQ_hom_zero (p: map f B ≤ A') : SQ_hom fA fB = 0:= by
  rw [LinearMap.ext_iff]
  apply Quot.ind
  intro a
  rw [SQ_hom_apply]
  simp
  rw [Submodule.Quotient.mk_eq_zero,mem_SQ_den]
  simp
  apply p
  apply mem_image_of_mem
  simp

theorem SQ_hom_comp : (SQ_hom fA fB) ≫ (SQ_hom gA gB) = @SQ_hom R _ X X'' (f ≫ g) A B A'' B'' (by apply map_lemma; repeat assumption) (by apply map_lemma; repeat assumption) := by
  rw [ModuleCat.comp_def,LinearMap.ext_iff]
  apply Quot.ind
  intro a
  rw [LinearMap.comp_apply,SQ_hom_apply,SQ_hom_apply,SQ_hom_apply]
  simp

theorem idmap (A :Submodule R X): map (CategoryStruct.id X) A = A := by
  ext x
  simp

theorem idcomap (A :Submodule R X): comap (CategoryStruct.id X) A = A := by
  rfl

def SQ_id_hom (A B A' B': Submodule R X){α : A ≤ A'}{β : B ≤ B'} : SQ A B ⟶  SQ A' B' := by
  apply SQ_hom
  pick_goal -1
  apply CategoryStruct.id
  repeat rw [idmap]; assumption

theorem SQ_ker_exact (o:A≤ B) (r:C = A + comap f A'⊓ B) : Exact (@SQ_id_hom R _ X A C A B (by rfl) (by rw [r];simp;assumption)) (SQ_hom fA fB) := by
  unfold SQ_id_hom
  rw [ModuleCat.exact_iff]
  apply le_antisymm
  rw [LinearMap.range_le_ker_iff,← ModuleCat.comp_def]
  rw [SQ_hom_comp]
  apply SQ_hom_zero
  rw [r]
  simp
  constructor
  assumption
  rw [inf_comm,comap_map_lemma2]
  simp
  apply Quot.ind
  intro a p
  simp at p
  simp
  rw [← Submodule.Quotient.quot_mk_eq_mk,SQ_hom_apply,Submodule.Quotient.quot_mk_eq_mk,Submodule.Quotient.mk_eq_zero,mem_SQ_den] at p
  simp at p
  have p1 : a.val ∈ A + comap f A' ⊓ B
  apply Submodule.mem_sup_right
  simp
  exact p
  rw [← r] at p1
  use (Quot.mk _ ⟨a.val,p1⟩)
  rw [SQ_hom_apply,Submodule.Quotient.quot_mk_eq_mk]
  rfl

def SQ_cok (f:X⟶ X')(B:Submodule R X)(A' B' :Submodule R X') : SQ A' B' ⟶  SQ (A' + map f B) B' := by
  apply SQ_id_hom
  apply le_sup_left
  rfl

theorem SQ_cok_exact (r: C' = A' + map f B): Exact (SQ_hom fA fB) (@SQ_id_hom R _ X' A' B' C' B' (by rw [r];simp) (by rfl)) := by
  unfold SQ_id_hom
  rw [ModuleCat.exact_iff]
  apply le_antisymm
  rw [LinearMap.range_le_ker_iff,← ModuleCat.comp_def]
  rw [SQ_hom_comp]
  apply SQ_hom_zero
  rw [r]
  simp
  apply Quot.ind
  intro a p
  simp
  simp at p
  rw [← Submodule.Quotient.quot_mk_eq_mk,SQ_hom_apply,Submodule.Quotient.quot_mk_eq_mk,Submodule.Quotient.mk_eq_zero,mem_SQ_den] at p
  rw [r] at p
  simp at p
  rw [mem_sup] at p
  rcases p with ⟨y,p1,z,p2,p3⟩
  simp at p2
  rcases p2 with ⟨u,p2,p4⟩
  use Quot.mk _ ⟨u,p2⟩
  rw [SQ_hom_apply,Quotient.quot_mk_eq_mk,Submodule.Quotient.eq,mem_SQ_den]
  simp
  rw [p4,← p3]
  conv => lhs; simp
  apply Submodule.neg_mem
  exact p1

theorem SQ_hom_mono (v : A ≤ B)(p : comap f A' ⊓ B ≤ A) : Mono (SQ_hom fA fB) := by
  apply mono_of_exact
  apply SQ_ker_exact
  assumption
  rfl
  apply SQ_zero
  simp
  assumption

theorem SQ_hom_epi (p : B' ≤ A' + map f B) : Epi (SQ_hom fA fB) := by
  apply epi_of_exact
  apply SQ_cok_exact
  rfl
  apply SQ_zero
  assumption

noncomputable def SQ_iso (v : A ≤ B)(p :comap f A' ⊓ B ≤ A)(q : B' ≤ A' + map f B) : SQ A B ≅ SQ A' B':= by
  have isosq : IsIso (SQ_hom fA fB) := by
    rw [isIso_iff_mono_and_epi]
    constructor
    apply SQ_hom_mono
    repeat assumption
    apply SQ_hom_epi
    repeat assumption
  exact @CategoryTheory.asIso _ _ _ _ _ isosq

def isomorphism_term1 := SQ (H ⊓ N) H

def isomorphism_term2 := SQ N (H + N)

noncomputable def isomorphism_iso : isomorphism_term1 N H ≅ isomorphism_term2 N H := by
  apply SQ_iso
  pick_goal -1
  apply 𝟙
  repeat rw [idmap]; simp
  repeat simp
  rw [idcomap]; simp
  rw [idmap]; simp

--begin formalization
theorem Submodule_modularprop (A B C : Submodule R X) (v: A ≤ C) : (A + B) ⊓ C = A + (B ⊓ C) := by
  apply sup_inf_assoc_of_le
  exact v

theorem Submodule_exchange_limit1 (p: Directed (fun x x1 => x ≤ x1) F) (A B : Submodule R X): ⨆ i:I ,(A + F i ⊓  B) = A + (⨆ i : I ,F i) ⊓ B := by
  apply le_antisymm
  apply iSup_le
  intro i
  apply left_add_right_inf_monotone
  apply le_iSup
  apply sup_le
  have i:I := Classical.ofNonempty
  apply le_trans
  swap
  apply le_iSup
  exact i
  simp
  intro x p
  cases' p with p1 p2
  simp at p1 p2
  rw [Submodule.mem_iSup_of_directed F p] at p1
  cases' p1 with i p1
  apply mem_iSup_of_mem
  swap
  exact i
  apply mem_sup_right
  constructor
  repeat assumption

theorem Submodule_exchange_limit2 (p: ∃ i0, IsMinOn F univ i0)(A B : Submodule R X): ⨅ i:I ,(A + F i ⊓  B)= A+ (⨅ i:I, F i) ⊓  B := by
  cases' p with i0 p
  have p1: ⨅ i:I ,(A + F i ⊓  B) = A+F i0⊓ B
  apply le_antisymm
  apply iInf_le
  apply le_iInf
  intro i
  apply left_add_right_inf_monotone
  apply p
  simp
  have p2: ⨅ i:I ,F i = F i0
  apply le_antisymm
  apply iInf_le
  apply le_iInf
  intro i
  apply p
  simp
  rw [p1,p2]

def Butterfly (A B C D: Submodule R X) := SQ (C + (A ⊓ D)) (C + (B ⊓ D))

def Butterfly' (A B C D: Submodule R X) := SQ  (B ⊓ C + A ⊓ D) (B ⊓ D)

theorem Butterfly'_iso_isomorphism_term1 (A B C D: Submodule R X)(v:A ≤ B)(w:C ≤ D) :Butterfly'  A B C D ≅ isomorphism_term1 (C + A ⊓ D) (B ⊓ D) := by
  unfold Butterfly'
  unfold isomorphism_term1
  simp
  rw [Lattice_lemma1]
  repeat assumption

theorem Butterfly_iso_isomorphism_term2 (A B C D: Submodule R X)(v:A ≤ B) :Butterfly A B C D ≅ isomorphism_term2 (C + A ⊓ D) (B ⊓ D) := by
  unfold Butterfly
  unfold isomorphism_term2
  simp
  rw [Lattice_lemma2]
  assumption

noncomputable def Butterfly'_iso_Butterfly (A B C D: Submodule R X)(v:A ≤ B)(w:C ≤ D) : Butterfly' A B C D ≅ Butterfly A B C D :=
calc
  Butterfly' A B C D ≅ isomorphism_term1 (C + A ⊓ D) (B ⊓ D) := by
    apply Butterfly'_iso_isomorphism_term1
    repeat assumption
  _ ≅ isomorphism_term2 (C + A ⊓ D) (B ⊓ D) := by
    apply isomorphism_iso
  _ ≅ Butterfly A B C D := by
    symm
    apply Butterfly_iso_isomorphism_term2
    assumption

def Butterfly'_symm_iso (A B C D: Submodule R X) :Butterfly'  A B C D ≅ Butterfly' C D A B
:= by
  unfold Butterfly'
  conv =>
    lhs
    congr
    · rw [inf_comm,add_comm,inf_comm]
    · rw [inf_comm]

noncomputable def Butterfly_symm_iso (A B C D: Submodule R X)(v:A ≤ B)(w:C ≤ D) : Butterfly A B C D ≅ Butterfly C D A B :=
calc
  Butterfly A B C D ≅ Butterfly' A B C D := by
    symm
    apply Butterfly'_iso_Butterfly
    repeat assumption
  _ ≅ Butterfly' C D A B := by
    apply Butterfly'_symm_iso
  _ ≅ Butterfly C D A B := by
    apply Butterfly'_iso_Butterfly
    repeat assumption

theorem map_sup_le : map f (A ⊔ B) ≤ A' ⊔ B' := by
  rw [Submodule.map_sup]
  apply sup_le_sup
  repeat assumption

theorem map_inf_le : map f (A ⊓ B) ≤ A' ⊓ B' := by
  intro x
  simp
  intro y p q r
  constructor
  rw [← r]
  apply fA
  apply mem_image_of_mem
  assumption
  rw [← r]
  apply fB
  apply mem_image_of_mem
  assumption

def Butterfly_functorial_hom : Butterfly A B C D ⟶ Butterfly A' B' C' D':= by
  apply SQ_hom
  pick_goal -1
  exact f
  repeat
    apply map_sup_le
    assumption
    apply map_inf_le
    repeat assumption

theorem Butterfly_functorial_mono (v:A≤ B)(w:C≤ D)(w':C'≤ D')(p: comap f (C'+A')= C+A): Mono (Butterfly_functorial_hom fA fB fC fD):= by
  apply SQ_hom_mono
  apply left_add_right_inf_monotone
  assumption
  intro x
  simp
  intro p1 p2
  rw [← sup_inf_assoc_of_le] at p1
  rw [← sup_inf_assoc_of_le]
  constructor
  simp at p
  rw [← p]
  simp
  exact p1.1
  have : C ⊔ (B ⊓ D) ≤ D
  rw [← sup_inf_assoc_of_le]
  simp
  swap
  apply this
  repeat assumption

theorem Butterfly_functorial_epi (p : map f (B⊓D)=B'⊓ D') : Epi (Butterfly_functorial_hom fA fB fC fD) := by
  apply SQ_hom_epi
  simp
  rw [p]
  constructor
  apply le_trans
  swap
  repeat apply le_sup_left
  apply le_trans
  swap
  repeat apply le_sup_right

noncomputable def Butterfly_functorial_iso (v:A≤ B)(w:C≤ D)(w':C'≤ D')(α : map f A =  A')(β : map f B= B')(γ : C= comap f C')(δ : D = comap f D') : Butterfly  A B C D ≅ Butterfly A' B' C' D' := by
  have fA: map f A ≤ A' := by rw [α]
  have fB: map f B ≤ B' := by rw [β]
  have fC: map f C ≤ C' := by
    rw [γ]
    apply image_preimage_subset
  have fD: map f D ≤ D' := by
    rw [δ]
    apply image_preimage_subset
  have isobf : IsIso (Butterfly_functorial_hom fA fB fC fD) := by
    rw [isIso_iff_mono_and_epi]
    constructor
    apply Butterfly_functorial_mono
    repeat assumption
    rw [← α,γ]
    apply comap_map_lemma1
    apply Butterfly_functorial_epi
    rw [← β,δ]
    apply comap_map_lemma2
  exact @CategoryTheory.asIso _ _ _ _ _ isobf
