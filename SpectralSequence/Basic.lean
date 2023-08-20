import SpectralSequence.FiltModule

import Mathlib.Algebra.Homology.Homology
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

open CategoryTheory Classical

def Categorytheory.Iso.pi {I : Type _} (C : I → Type _ ) [inst : (i : I) → CategoryTheory.Category (C i)] (A B : (i : I) → C i) (p:∀i, A i ≅ B i) : A ≅ B where
  hom := by
    unfold pi'
    unfold pi
    simp
    intro i
    exact (p i).hom
  inv := by
    unfold pi'
    unfold pi
    simp
    intro i
    exact (p i).inv

noncomputable def homology.mapIso' (V : _)[Category V] [Abelian V] {A1 B1 C1 A2 B2 C2: V}(f1:A1⟶B1)(g1:B1⟶C1)(f2:A2⟶ B2)(g2:B2⟶C2)(α:A1≅A2)(β: B1≅B2)(γ:C1≅C2)(s:α.1 ≫ f2 = f1 ≫ β.1)(t:β.1≫g2=g1≫γ.1)(w:f1≫g1=0):homology f1 g1 w ≅ homology f2 g2 (by
  have : α.1 ≫ (f2≫ g2) ≫ γ.2 ≫ γ.1 =f1 ≫ g1 ≫ γ.1
  simp
  rw [← Category.assoc,s,← t,Category.assoc]
  conv at this => rhs; rw [← Category.assoc,w]
  simp at this
  exact this) := by
  apply homology.mapIso
  pick_goal -1
  apply CategoryTheory.Arrow.isoMk
  exact t
  pick_goal 2
  apply CategoryTheory.Arrow.isoMk
  exact s
  simp

def SpectralSequencePageShape (r : ℤ): ComplexShape (ℤ×ℤ) where
  Rel i j := (j.1 = i.1 - r) ∧ (j.2 = i.2 + r - 1)
  next_eq := by
    intro i j j' hi hj
    ext
    rw [hi.1,hj.1]
    rw [hi.2,hj.2]
  prev_eq := by
    intro i i' j hi hi'
    ext
    have : i.fst - r = i'.fst - r
    rw [← hi.1,← hi'.1]
    linarith
    have : i.snd + r - 1 = i'.snd + r - 1
    rw [← hi.2,← hi'.2]
    linarith

theorem shape_lemma (r : ℤ): ∀ p q, (SpectralSequencePageShape r).Rel (p,q) (p-r,q+r-1) := by
  intro p q
  unfold SpectralSequencePageShape
  dsimp
  constructor
  repeat rfl

variable (V : _) [Category V] [Abelian V]

abbrev SpectralSequencePage (r : ℤ) := HomologicalComplex V (SpectralSequencePageShape r)

structure SpectralSequence (E : (r : ℤ) → SpectralSequencePage V r) where
  NextPage : (E (r + 1)).X ≅ (E r).homology

namespace filtModuleHomologoicalComplex

variable {R:Type _}[Ring R]{C: HomologicalComplex (FiltModuleCat R) (ComplexShape.down ℤ)}

noncomputable def d_ss (r : ℤ) (i j : ℤ×ℤ): @E R _ C r i.1 i.2 ⟶ @E R _ C r j.1 j.2 := by
  by_cases (SpectralSequencePageShape r).Rel i j
  unfold SpectralSequencePageShape at h
  dsimp at h
  rw [h.1,h.2]
  apply d
  apply 0

set_option maxHeartbeats 1000000000
theorem d_ss_apply1 (r p q: ℤ): @d_ss R _ C r (p,q) (p-r,q+r-1) = d r p q := by
  unfold d_ss
  rw [dite_eq_iff]
  left
  use shape_lemma r p q
  rfl

theorem d_ss_apply2 (r: ℤ)(i j :ℤ × ℤ)(h: ¬(SpectralSequencePageShape r).Rel i j  ): @d_ss R _ C r i j = 0 := by
  unfold d_ss
  rw [dite_eq_iff]
  right
  use h

set_option maxHeartbeats 1000000000
noncomputable def E_ss (r : ℤ) : SpectralSequencePage (ModuleCat R) r where
  X i := @E R _ C r i.1 i.2
  d i j := @d_ss R _ C r i j
  shape := by
    intro i j h
    dsimp
    apply d_ss_apply2
    assumption
  d_comp_d' := by
    intro i j k s t
    dsimp
    cases' i with p q
    cases' j with p' q'
    cases' k with p'' q''
    unfold SpectralSequencePageShape at s t
    dsimp at s t
    rw [t.1,t.2,s.1,s.2]
    rw [d_ss_apply1,d_ss_apply1]
    apply d_diff
    repeat assumption

theorem E_ss_d (r p q : ℤ): (@E_ss R _ C r).d (p,q) (p-r,q+r-1) = @d R _ C r p q := by
  unfold E_ss
  dsimp
  apply d_ss_apply1

noncomputable instance SpectralSequence : SpectralSequence (ModuleCat R) (@E_ss R _ C) where
  NextPage := by
    intro r
    apply Categorytheory.Iso.pi
    intro i
    cases' i with p' q'
    let p := p' + r
    have h1 : p' = p - r
    simp
    let q := q' + 1 - r
    have h2 : q' = q + r - 1
    simp
    rw [h1,h2]
    have h3 : HomologicalComplex.X (E_ss (r + 1)) (p-r, q+r-1) = @E R _ C (r+1) (p-r) (q+r-1)
    rfl
    have h4 : HomologicalComplex.homology (@E_ss R _ C r) (p - r, q + r - 1) ≅ homology (d r p q) (d r (p-r) (q+r-1)) (@d_diff R _ C r p q)
    apply Iso.trans
    exact HomologicalComplex.homologyIso (E_ss r) (by apply shape_lemma) (by apply shape_lemma)
    apply homology.mapIso'
    pick_goal -2
    rfl
    pick_goal -2
    rfl
    pick_goal -2
    rfl
    rw [E_ss_d]
    unfold Iso.refl
    simp
    rw [E_ss_d]
    unfold Iso.refl
    simp
    rw [h3]
    apply Iso.trans
    swap
    symm
    exact h4
    symm
    apply homology_of_E
