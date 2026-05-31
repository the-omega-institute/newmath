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

theorem DecimalExpansionNonescape [AskSetup] [PackageSetup]
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
                                                    hsame row publicRead ∧ UnaryHistory row)
                                                  (fun row : BHist =>
                                                    hsame row D ∨ hsame row W ∨
                                                      hsame row V ∨ hsame row Q ∨
                                                        hsame row R ∨ hsame row E ∨
                                                          hsame row publicRead)
                                                  (fun row : BHist =>
                                                    UnaryHistory row ∧
                                                      PkgSig bundle publicRead pkg)
                                                  hsame ∧
                                                UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro dUnary wUnary vUnary qUnary rUnary eUnary hUnary cUnary pUnary nUnary
    digitWindowCont placeValueCont dyadicCont regseqCont realSealCont transportCont
    replayCont provenanceCont nameRouteCont publicPkg publicSame
  have digitWindowUnary : UnaryHistory digitWindow :=
    unary_cont_closed dUnary wUnary digitWindowCont
  have placeValueUnary : UnaryHistory placeValue :=
    unary_cont_closed digitWindowUnary vUnary placeValueCont
  have dyadicUnary : UnaryHistory dyadic :=
    unary_cont_closed placeValueUnary qUnary dyadicCont
  have regseqUnary : UnaryHistory regseq :=
    unary_cont_closed dyadicUnary rUnary regseqCont
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqUnary eUnary realSealCont
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed realSealUnary hUnary transportCont
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed transportUnary cUnary replayCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed replayUnary pUnary provenanceCont
  have nameRouteUnary : UnaryHistory nameRoute :=
    unary_cont_closed provenanceUnary nUnary nameRouteCont
  have publicUnary : UnaryHistory publicRead :=
    unary_transport_symm nameRouteUnary publicSame
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row V ∨ hsame row Q ∨
              hsame row R ∨ hsame row E ∨ hsame row publicRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, publicPkg⟩
    }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.DecimalExpansionUp
