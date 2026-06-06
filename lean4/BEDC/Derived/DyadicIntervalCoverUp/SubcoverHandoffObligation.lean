import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverSubcoverHandoffObligation [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead coverRead readbackRead sealRead
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont L U endpointRead →
        Cont M R coverRead →
          Cont W Q readbackRead →
            Cont readbackRead A sealRead →
              Cont coverRead sealRead handoffRead →
                PkgSig bundle handoffRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
                          hsame row V ∨ hsame row W ∨ hsame row Q ∨ hsame row A ∨
                            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                              hsame row handoffRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont L U endpointRead ∧
                          Cont M R coverRead ∧ Cont W Q readbackRead ∧
                            Cont readbackRead A sealRead ∧
                              Cont coverRead sealRead handoffRead ∧
                                PkgSig bundle handoffRead pkg)
                      hsame ∧
                    UnaryHistory endpointRead ∧ UnaryHistory coverRead ∧
                      UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro surface endpointRoute coverRoute readbackRoute sealRoute handoffRoute handoffPkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary uUnary endpointRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed mUnary rUnary coverRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed wUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary aUnary sealRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed coverUnary sealUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
              hsame row W ∨ hsame row Q ∨ hsame row A ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U endpointRead ∧ Cont M R coverRead ∧
              Cont W Q readbackRead ∧ Cont readbackRead A sealRead ∧
                Cont coverRead sealRead handoffRead ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointRoute, coverRoute, readbackRoute, sealRoute,
          handoffRoute, handoffPkg⟩
  }
  exact
    ⟨cert, endpointUnary, coverUnary, readbackUnary, sealUnary, handoffUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
