/-
Prompt 02, item 8: closure of a Schur-type essential image under AMBIENT subobjects and
quotients, keeping the actual inclusion.

Setting: abelian categories `P`, `R`; an exact functor `F : P ⥤ R` with a right adjoint `G`
whose counit `F G ⟶ 𝟭` is an isomorphism (for the Schur functor: source §7.3, `F G ≅ id`).
`S` is a class of objects of `P` closed under subobjects and quotients (e.g. a Serre class),
and `B = essential image of S under F`.

* `subobject_lift`: for a monomorphism `i : Y ⟶ F X` there are `X' ↪ X` and `e : F X' ≅ Y`
  with `F (X' ↪ X) = e ≫ i`.  (Pull back `G Y ⟶ G F X` along the unit `X ⟶ G F X`.)
* `image_closed_under_subobjects`, `image_closed_under_quotients`.

Not assumed: that `G` preserves `S`, that `F` is full, or that the image is closed under
extensions.  No hypothesis beyond those displayed.
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.ObjectProperty.EpiMono
import DegreeProfilesReview.PCTransport

open CategoryTheory CategoryTheory.Limits

namespace DegreeProfilesReview.ImageClosure

universe v v' u u'

variable {P : Type u} [Category.{v} P] [Abelian P] {R : Type u'} [Category.{v'} R] [Abelian R]
variable (F : P ⥤ R) (G : R ⥤ P) (adj : F ⊣ G) [IsIso adj.counit]

include adj in
/-- Lifting an ambient subobject of `F X` to a subobject of `X`, with the actual inclusion. -/
theorem subobject_lift [PreservesFiniteLimits F] {X : P} {Y : R} (i : Y ⟶ F.obj X) [Mono i] :
    ∃ (X' : P) (j : X' ⟶ X) (_ : Mono j) (e : F.obj X' ≅ Y), F.map j = e.hom ≫ i := by
  haveI : G.PreservesMonomorphisms := Functor.preservesMonomorphisms_of_adjunction adj
  haveI : Mono (G.map i) := inferInstance
  haveI hη : IsIso (F.map (adj.unit.app X)) := by
    have h := adj.left_triangle_components X
    haveI : IsIso (F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X)) := by
      rw [h]; exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app (F.obj X))
  refine ⟨pullback (G.map i) (adj.unit.app X), pullback.snd _ _, inferInstance,
    PreservesPullback.iso F (G.map i) (adj.unit.app X) ≪≫
      asIso (pullback.fst (F.map (G.map i)) (F.map (adj.unit.app X))) ≪≫
      asIso (adj.counit.app Y), ?_⟩
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← adj.counit_naturality i, ← Category.assoc (pullback.fst _ _), pullback.condition,
    Category.assoc, adj.left_triangle_components]
  erw [Category.comp_id]
  rw [PreservesPullback.iso_hom_snd]

/-- The essential image of a class `S` of objects under `F`. -/
def image (S : ObjectProperty P) : ObjectProperty R :=
  fun Y => ∃ X, S X ∧ Nonempty (F.obj X ≅ Y)

include adj in
/-- The image of a subobject-closed class is closed under ambient subobjects. -/
theorem image_closed_under_subobjects [PreservesFiniteLimits F] (S : ObjectProperty P)
    [S.IsClosedUnderSubobjects] {Y₁ Y₂ : R} (i : Y₁ ⟶ Y₂) [Mono i] (h : image F S Y₂) :
    image F S Y₁ := by
  obtain ⟨X, hX, ⟨a⟩⟩ := h
  obtain ⟨X', j, _, e, _⟩ := subobject_lift F G adj (i ≫ a.inv)
  exact ⟨X', S.prop_of_mono j hX, ⟨e⟩⟩

include adj in
/-- The image of a class closed under subobjects and quotients is closed under ambient
quotients. -/
theorem image_closed_under_quotients [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (S : ObjectProperty P)
    [S.IsClosedUnderQuotients] {Y Z : R} (p : Y ⟶ Z) [Epi p] (h : image F S Y) :
    image F S Z := by
  obtain ⟨X, hX, ⟨a⟩⟩ := h
  -- the kernel of `F X ≅ Y ⟶ Z`, as an ambient subobject of `F X`
  let p' : F.obj X ⟶ Z := a.hom ≫ p
  haveI : Epi p' := epi_comp _ _
  obtain ⟨X', j, _, e, hj⟩ := subobject_lift F G adj (kernel.ι p')
  obtain ⟨q, _⟩ := Transport.cokernel_transport F j (kernel.ι p') e (Iso.refl _)
    (by rw [Iso.refl_hom, Category.comp_id, hj])
  have hcolim := Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι p') (kernel.condition p'))
    (kernelIsKernel p')
  let z : cokernel (kernel.ι p') ≅ Z :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hcolim
  exact ⟨cokernel j, S.prop_of_epi (cokernel.π j) hX, ⟨q ≪≫ z⟩⟩

end DegreeProfilesReview.ImageClosure
