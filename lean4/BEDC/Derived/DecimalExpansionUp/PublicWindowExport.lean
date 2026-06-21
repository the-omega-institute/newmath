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

theorem DecimalExpansionPublicWindowExport [AskSetup] [PackageSetup]
    {D W V Q R E H C P N prefixRead placeRead toleranceRead regseqRead sealRead replayRead
      namedRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D →
      UnaryHistory W →
        UnaryHistory V →
          UnaryHistory Q →
            UnaryHistory R →
              UnaryHistory E →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory P →
                      UnaryHistory N →
                        Cont D W prefixRead →
                          Cont prefixRead V placeRead →
                            Cont placeRead Q toleranceRead →
                              Cont toleranceRead R regseqRead →
                                Cont regseqRead E sealRead →
                                  Cont sealRead C replayRead →
                                    Cont replayRead N namedRead →
                                      Cont namedRead E publicRead →
                                        PkgSig bundle P pkg →
                                          PkgSig bundle publicRead pkg →
                                            SemanticNameCert
                                                (fun row : BHist =>
                                                  hsame row publicRead ∧ UnaryHistory row)
                                                (fun row : BHist =>
                                                  hsame row D ∨ hsame row W ∨
                                                    hsame row V ∨ hsame row Q ∨
                                                      hsame row R ∨ hsame row E ∨
                                                        hsame row N ∨ hsame row publicRead)
                                                (fun row : BHist =>
                                                  UnaryHistory row ∧ Cont D W prefixRead ∧
                                                    Cont toleranceRead R regseqRead ∧
                                                      Cont regseqRead E sealRead ∧
                                                        PkgSig bundle publicRead pkg)
                                                hsame ∧
                                              UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame SemanticNameCert
  intro dUnary wUnary vUnary qUnary rUnary eUnary _hUnary cUnary _pUnary nUnary prefixRoute
    placeRoute toleranceRoute regseqRoute sealRoute replayRoute namedRoute publicRoute
    _provenancePkg publicPkg
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed dUnary wUnary prefixRoute
  have placeUnary : UnaryHistory placeRead :=
    unary_cont_closed prefixUnary vUnary placeRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed placeUnary qUnary toleranceRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed toleranceUnary rUnary regseqRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary eUnary sealRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed sealUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nUnary namedRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed namedUnary eUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row V ∨ hsame row Q ∨ hsame row R ∨
              hsame row E ∨ hsame row N ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W prefixRead ∧ Cont toleranceRead R regseqRead ∧
              Cont regseqRead E sealRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, prefixRoute, regseqRoute, sealRoute, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.DecimalExpansionUp
