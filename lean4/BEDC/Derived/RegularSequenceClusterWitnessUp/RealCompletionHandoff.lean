import BEDC.Derived.RegularSequenceClusterWitnessUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularSequenceClusterWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularSequenceClusterWitnessRealCompletionHandoff [AskSetup] [PackageSetup]
    {source finiteWindow extractor dyadic readback sealRow transport replay provenance localName
      clusterRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory finiteWindow ->
        UnaryHistory extractor ->
          UnaryHistory dyadic ->
            UnaryHistory readback ->
              UnaryHistory sealRow ->
                UnaryHistory replay ->
                  Cont source finiteWindow extractor ->
                    Cont extractor dyadic readback ->
                      Cont readback sealRow clusterRead ->
                        Cont clusterRead replay completionRead ->
                          PkgSig bundle provenance pkg ->
                            PkgSig bundle localName pkg ->
                              PkgSig bundle completionRead pkg ->
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row completionRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row source ∨ hsame row finiteWindow ∨
                                        hsame row extractor ∨ hsame row dyadic ∨
                                          hsame row readback ∨ hsame row sealRow ∨
                                            hsame row completionRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont source finiteWindow extractor ∧
                                        Cont extractor dyadic readback ∧
                                          Cont readback sealRow clusterRead ∧
                                            Cont clusterRead replay completionRead ∧
                                              PkgSig bundle completionRead pkg)
                                    hsame ∧
                                  UnaryHistory clusterRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro sourceUnary finiteWindowUnary extractorUnary dyadicUnary readbackUnary sealRowUnary
    replayUnary sourceRoute readbackRoute clusterRoute completionRoute _provenancePkg
    _localNamePkg completionPkg
  have clusterUnary : UnaryHistory clusterRead :=
    unary_cont_closed readbackUnary sealRowUnary clusterRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed clusterUnary replayUnary completionRoute
  have sourceAtCompletion :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row) completionRead :=
    ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row finiteWindow ∨ hsame row extractor ∨
              hsame row dyadic ∨ hsame row readback ∨ hsame row sealRow ∨
                hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source finiteWindow extractor ∧
              Cont extractor dyadic readback ∧ Cont readback sealRow clusterRead ∧
                Cont clusterRead replay completionRead ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceAtCompletion
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
      exact
        ⟨source.right, sourceRoute, readbackRoute, clusterRoute, completionRoute,
          completionPkg⟩
  }
  exact ⟨cert, clusterUnary, completionUnary⟩

end BEDC.Derived.RegularSequenceClusterWitnessUp
