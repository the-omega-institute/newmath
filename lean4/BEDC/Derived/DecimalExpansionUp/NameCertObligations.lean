import BEDC.Derived.DecimalExpansionUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DecimalExpansionNameCertObligations [AskSetup] [PackageSetup]
    {D W V Q R E H C P N prefixRead comparison handoff sealRead replayRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D →
      UnaryHistory W →
        UnaryHistory V →
          UnaryHistory Q →
            UnaryHistory R →
              UnaryHistory E →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory N →
                      Cont D W prefixRead →
                        Cont prefixRead V comparison →
                          Cont comparison Q handoff →
                            Cont handoff R sealRead →
                              Cont H C replayRead →
                                Cont P N namedRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      SemanticNameCert
                                          (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row N ∧
                                              Cont D W prefixRead ∧
                                                Cont prefixRead V comparison ∧
                                                  Cont comparison Q handoff ∧
                                                    Cont handoff R sealRead)
                                          (fun row : BHist =>
                                            hsame row N ∧ PkgSig bundle P pkg ∧
                                              PkgSig bundle N pkg)
                                          hsame ∧
                                        UnaryHistory prefixRead ∧
                                          UnaryHistory comparison ∧
                                            UnaryHistory handoff ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro dUnary wUnary vUnary qUnary rUnary _eUnary _hUnary _cUnary nUnary
    digitWindow prefixPlace comparisonDyadic handoffRegular _transportReplay _provenanceName
    provenancePkg namePkg
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed dUnary wUnary digitWindow
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed prefixUnary vUnary prefixPlace
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed comparisonUnary qUnary comparisonDyadic
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary rUnary handoffRegular
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row N ∧
              Cont D W prefixRead ∧
                Cont prefixRead V comparison ∧
                  Cont comparison Q handoff ∧ Cont handoff R sealRead)
          (fun row : BHist =>
            hsame row N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
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
          intro _row other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.left, digitWindow, prefixPlace, comparisonDyadic, handoffRegular⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, provenancePkg, namePkg⟩
    }
  exact ⟨cert, prefixUnary, comparisonUnary, handoffUnary, sealUnary⟩

end BEDC.Derived.DecimalExpansionUp
