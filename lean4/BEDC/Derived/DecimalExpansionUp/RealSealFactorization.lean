import BEDC.Derived.DecimalExpansionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
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

theorem DecimalExpansionRealSealFactorization [AskSetup] [PackageSetup]
    {D W V Q R E H C P N digitWindow placeValue dyadic regseq realSeal transport replay
      provenance nameRoute publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D ->
      UnaryHistory W ->
        UnaryHistory V ->
          UnaryHistory Q ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        Cont D W digitWindow ->
                          Cont digitWindow V placeValue ->
                            Cont placeValue Q dyadic ->
                              Cont dyadic R regseq ->
                                Cont regseq E realSeal ->
                                  Cont realSeal H transport ->
                                    Cont transport C replay ->
                                      Cont replay P provenance ->
                                        Cont provenance N nameRoute ->
                                          PkgSig bundle publicRead pkg ->
                                            hsame publicRead nameRoute ->
                                              SemanticNameCert
                                                  (fun row : BHist =>
                                                    hsame row publicRead ∧
                                                      UnaryHistory row)
                                                  (fun row : BHist =>
                                                    hsame row D ∨ hsame row W ∨
                                                      hsame row V ∨ hsame row Q ∨
                                                        hsame row R ∨ hsame row E ∨
                                                          hsame row publicRead)
                                                  (fun row : BHist =>
                                                    UnaryHistory row ∧
                                                      PkgSig bundle publicRead pkg)
                                                  hsame ∧
                                                UnaryHistory realSeal ∧
                                                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary eUnary hUnary cUnary pUnary nUnary
    digitWindowRoute placeValueRoute dyadicRoute regseqRoute realSealRoute transportRoute
    replayRoute provenanceRoute nameRouteRoute publicPkg publicSameName
  have digitWindowUnary : UnaryHistory digitWindow :=
    unary_cont_closed dUnary wUnary digitWindowRoute
  have placeValueUnary : UnaryHistory placeValue :=
    unary_cont_closed digitWindowUnary vUnary placeValueRoute
  have dyadicUnary : UnaryHistory dyadic :=
    unary_cont_closed placeValueUnary qUnary dyadicRoute
  have regseqUnary : UnaryHistory regseq :=
    unary_cont_closed dyadicUnary rUnary regseqRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqUnary eUnary realSealRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed realSealUnary hUnary transportRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed transportUnary cUnary replayRoute
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed replayUnary pUnary provenanceRoute
  have nameRouteUnary : UnaryHistory nameRoute :=
    unary_cont_closed provenanceUnary nUnary nameRouteRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_transport_symm nameRouteUnary publicSameName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row V ∨ hsame row Q ∨ hsame row R ∨
              hsame row E ∨ hsame row publicRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicPkg⟩
  }
  exact ⟨cert, realSealUnary, publicUnary⟩

end BEDC.Derived.DecimalExpansionUp
