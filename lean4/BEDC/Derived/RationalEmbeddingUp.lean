import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RationalEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RationalEmbeddingCarrier [AskSetup] [PackageSetup]
    (q S R D E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory q ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RationalEmbeddingCarrier_constant_sequence_route [AskSetup] [PackageSetup]
    {q S R D E H C P N scheduleRead readbackRead dyadicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalEmbeddingCarrier q S R D E H C P N bundle pkg →
      Cont q S scheduleRead →
        Cont scheduleRead R readbackRead →
          Cont readbackRead D dyadicRead →
            PkgSig bundle P pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row R ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                      hsame row dyadicRead)
                  (fun _row : BHist =>
                    UnaryHistory _row ∧ Cont q S scheduleRead ∧
                      Cont scheduleRead R readbackRead ∧ Cont readbackRead D dyadicRead ∧
                        PkgSig bundle P pkg)
                  hsame ∧
                UnaryHistory scheduleRead ∧ UnaryHistory readbackRead ∧
                  UnaryHistory dyadicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier routeSchedule routeReadback routeDyadic provenance
  obtain ⟨unaryQ, unaryS, unaryR, unaryD, _unaryE, _unaryH, _unaryC, _unaryP,
    _unaryN, _carrierPkg, _carrierName⟩ := carrier
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed unaryQ unaryS routeSchedule
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed scheduleUnary unaryR routeReadback
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed readbackUnary unaryD routeDyadic
  have sourceR :
      (fun row : BHist => hsame row R ∧ UnaryHistory row) R := by
    exact ⟨hsame_refl R, unaryR⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row R ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
              hsame row dyadicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q S scheduleRead ∧
              Cont scheduleRead R readbackRead ∧ Cont readbackRead D dyadicRead ∧
                PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro R sourceR
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right
      right
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeSchedule, routeReadback, routeDyadic, provenance⟩
  }
  exact ⟨cert, scheduleUnary, readbackUnary, dyadicUnary⟩

end BEDC.Derived.RationalEmbeddingUp
