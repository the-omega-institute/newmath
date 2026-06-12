import BEDC.Derived.CauchyUp

namespace BEDC.Derived.CauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyPublicL10Export [AskSetup] [PackageSetup]
    {stream request dyadic readback realSeal transport replay provenance localName
      requestRead toleranceRead rationalRead sealRead structuralRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory stream ->
      UnaryHistory request ->
        UnaryHistory dyadic ->
          UnaryHistory readback ->
            UnaryHistory realSeal ->
              UnaryHistory transport ->
                UnaryHistory replay ->
                  UnaryHistory provenance ->
                    UnaryHistory localName ->
                      Cont stream request requestRead ->
                        Cont requestRead dyadic toleranceRead ->
                          Cont toleranceRead readback rationalRead ->
                            Cont rationalRead realSeal sealRead ->
                              Cont transport replay structuralRead ->
                                Cont provenance localName namedRead ->
                                  PkgSig bundle provenance pkg ->
                                    PkgSig bundle localName pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row sealRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row stream ∨ hsame row request ∨
                                              hsame row dyadic ∨ hsame row readback ∨
                                                hsame row realSeal ∨ hsame row sealRead ∨
                                                  hsame row structuralRead ∨
                                                    hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧
                                              PkgSig bundle provenance pkg ∧
                                                PkgSig bundle localName pkg)
                                          hsame ∧
                                        UnaryHistory requestRead ∧
                                          UnaryHistory toleranceRead ∧
                                            UnaryHistory rationalRead ∧
                                              UnaryHistory sealRead ∧
                                                UnaryHistory structuralRead ∧
                                                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro streamUnary requestUnary dyadicUnary readbackUnary realSealUnary transportUnary
    replayUnary provenanceUnary localNameUnary requestRoute toleranceRoute rationalRoute
    sealRoute structuralRoute namedRoute provenancePkg localNamePkg
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed streamUnary requestUnary requestRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed requestReadUnary dyadicUnary toleranceRoute
  have rationalReadUnary : UnaryHistory rationalRead :=
    unary_cont_closed toleranceReadUnary readbackUnary rationalRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed rationalReadUnary realSealUnary sealRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed transportUnary replayUnary structuralRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed provenanceUnary localNameUnary namedRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealReadUnary⟩
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro sealRead sourceSeal
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, localNamePkg⟩
    }
  · exact
      ⟨requestReadUnary, toleranceReadUnary, rationalReadUnary, sealReadUnary,
        structuralReadUnary, namedReadUnary⟩

end BEDC.Derived.CauchyUp
