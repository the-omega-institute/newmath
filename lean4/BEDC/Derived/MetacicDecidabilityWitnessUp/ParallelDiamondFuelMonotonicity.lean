import BEDC.Derived.MetacicDecidabilityWitnessUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetacicDecidabilityWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicParallelDiamondFuelMonotonicity [AskSetup] [PackageSetup]
    {T S B F R H C P N D checkerRead boundedRead normalRead diamondRead
      enlargedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory S →
        UnaryHistory B →
          UnaryHistory F →
            UnaryHistory R →
              UnaryHistory D →
                UnaryHistory C →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      Cont T S checkerRead →
                        Cont B F boundedRead →
                          Cont checkerRead boundedRead normalRead →
                            Cont normalRead D diamondRead →
                              Cont diamondRead R enlargedRead →
                                Cont C P N →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row enlargedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row T ∨ hsame row S ∨ hsame row B ∨
                                          hsame row F ∨ hsame row R ∨ hsame row D ∨
                                            hsame row normalRead ∨
                                              hsame row diamondRead ∨
                                                hsame row enlargedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont T S checkerRead ∧
                                          Cont B F boundedRead ∧
                                            Cont checkerRead boundedRead normalRead ∧
                                              Cont normalRead D diamondRead ∧
                                                Cont diamondRead R enlargedRead ∧
                                                  Cont C P N ∧ PkgSig bundle P pkg ∧
                                                    PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory checkerRead ∧ UnaryHistory boundedRead ∧
                                      UnaryHistory normalRead ∧ UnaryHistory diamondRead ∧
                                        UnaryHistory enlargedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro TUnary SUnary BUnary FUnary RUnary DUnary CUnary pkgP pkgN checkerRoute
    boundedRoute normalRoute diamondRoute enlargedRoute replayRoute
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed TUnary SUnary checkerRoute
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed BUnary FUnary boundedRoute
  have normalUnary : UnaryHistory normalRead :=
    unary_cont_closed checkerUnary boundedUnary normalRoute
  have diamondUnary : UnaryHistory diamondRead :=
    unary_cont_closed normalUnary DUnary diamondRoute
  have enlargedUnary : UnaryHistory enlargedRead :=
    unary_cont_closed diamondUnary RUnary enlargedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row enlargedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row F ∨ hsame row R ∨
              hsame row D ∨ hsame row normalRead ∨ hsame row diamondRead ∨
                hsame row enlargedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T S checkerRead ∧ Cont B F boundedRead ∧
              Cont checkerRead boundedRead normalRead ∧ Cont normalRead D diamondRead ∧
                Cont diamondRead R enlargedRead ∧ Cont C P N ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro enlargedRead
        ⟨hsame_refl enlargedRead, enlargedUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, checkerRoute, boundedRoute, normalRoute, diamondRoute,
          enlargedRoute, replayRoute, pkgP, pkgN⟩
  }
  exact
    ⟨cert, checkerUnary, boundedUnary, normalUnary, diamondUnary, enlargedUnary⟩

end BEDC.Derived.MetacicDecidabilityWitnessUp
