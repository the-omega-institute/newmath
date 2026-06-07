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

theorem DyadicIntervalCoverSubcoverExclusionObligation [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead coverRead membershipRead transportRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont L U endpointRead →
        Cont M R coverRead →
          Cont coverRead V membershipRead →
            Cont H membershipRead transportRead →
              Cont transportRead C replayRead →
                PkgSig bundle replayRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
                          hsame row V ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                            hsame row N ∨ hsame row replayRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont L U endpointRead ∧
                          Cont M R coverRead ∧ Cont coverRead V membershipRead ∧
                            Cont H membershipRead transportRead ∧
                              Cont transportRead C replayRead ∧
                                PkgSig bundle replayRead pkg)
                      hsame ∧
                    UnaryHistory endpointRead ∧ UnaryHistory coverRead ∧
                      UnaryHistory membershipRead ∧ UnaryHistory transportRead ∧
                        UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro surface endpointRoute coverRoute membershipRoute transportRoute replayRoute replayPkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have vUnary : UnaryHistory V := surface.right.right.right.right.left
  have hUnary : UnaryHistory H :=
    surface.right.right.right.right.right.right.right.right.left
  have cUnary : UnaryHistory C :=
    surface.right.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary uUnary endpointRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed mUnary rUnary coverRoute
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed coverUnary vUnary membershipRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed hUnary membershipUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
              hsame row V ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U endpointRead ∧ Cont M R coverRead ∧
              Cont coverRead V membershipRead ∧ Cont H membershipRead transportRead ∧
                Cont transportRead C replayRead ∧ PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointRoute, coverRoute, membershipRoute, transportRoute,
          replayRoute, replayPkg⟩
  }
  exact
    ⟨cert, endpointUnary, coverUnary, membershipUnary, transportUnary, replayUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
