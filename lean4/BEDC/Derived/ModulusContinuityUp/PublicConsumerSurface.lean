import BEDC.Derived.ModulusContinuityUp.CompositionRoute
import BEDC.Derived.ModulusContinuityUp.UniformCauchyHandoff

namespace BEDC.Derived.ModulusContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ModulusContinuityPublicConsumerSurface [AskSetup] [PackageSetup]
    {graph sourceWindow modulus dyadic readback realSeal _htransport replay provenance localName
      toleranceRead windowRead graphRead readbackRead realRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory graph ->
      UnaryHistory sourceWindow ->
        UnaryHistory modulus ->
          UnaryHistory dyadic ->
            UnaryHistory readback ->
              UnaryHistory realSeal ->
                UnaryHistory replay ->
                  Cont dyadic modulus toleranceRead ->
                    Cont toleranceRead sourceWindow windowRead ->
                      Cont windowRead graph graphRead ->
                        Cont graphRead readback readbackRead ->
                          Cont readbackRead realSeal realRead ->
                            Cont realRead replay publicRead ->
                              PkgSig bundle provenance pkg ->
                                PkgSig bundle localName pkg ->
                                  PkgSig bundle publicRead pkg ->
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row publicRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row dyadic ∨ hsame row modulus ∨
                                            hsame row sourceWindow ∨ hsame row graph ∨
                                              hsame row readback ∨ hsame row realSeal ∨
                                                hsame row publicRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧
                                            Cont dyadic modulus toleranceRead ∧
                                              Cont toleranceRead sourceWindow windowRead ∧
                                                Cont windowRead graph graphRead ∧
                                                  Cont graphRead readback readbackRead ∧
                                                    Cont readbackRead realSeal realRead ∧
                                                      Cont realRead replay publicRead ∧
                                                        PkgSig bundle provenance pkg ∧
                                                          PkgSig bundle localName pkg ∧
                                                            PkgSig bundle publicRead pkg)
                                        hsame ∧
                                      UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro graphUnary sourceWindowUnary modulusUnary dyadicUnary readbackUnary realSealUnary
    replayUnary toleranceRoute windowRoute graphRoute readbackRoute realRoute publicRoute
    provenancePkg localNamePkg publicPkg
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed dyadicUnary modulusUnary toleranceRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceUnary sourceWindowUnary windowRoute
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed windowUnary graphUnary graphRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed graphReadUnary readbackUnary readbackRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed readbackReadUnary realSealUnary realRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed realReadUnary replayUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row modulus ∨ hsame row sourceWindow ∨
              hsame row graph ∨ hsame row readback ∨ hsame row realSeal ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont dyadic modulus toleranceRead ∧
              Cont toleranceRead sourceWindow windowRead ∧ Cont windowRead graph graphRead ∧
                Cont graphRead readback readbackRead ∧ Cont readbackRead realSeal realRead ∧
                  Cont realRead replay publicRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
        ⟨source.right, toleranceRoute, windowRoute, graphRoute, readbackRoute, realRoute,
          publicRoute, provenancePkg, localNamePkg, publicPkg⟩
  }
  exact ⟨cert, publicReadUnary⟩

end BEDC.Derived.ModulusContinuityUp
