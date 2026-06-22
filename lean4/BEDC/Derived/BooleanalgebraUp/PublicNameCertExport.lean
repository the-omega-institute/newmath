import BEDC.Derived.BooleanalgebraUp

namespace BEDC.Derived.BooleanalgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BooleanAlgebraCarrier_public_namecert_export [AskSetup] [PackageSetup]
    {join meet compl zero one order transport replay provenance localName endpoint
      booleanSource stoneRead regularRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BooleanAlgebraCarrier join meet compl zero one order transport replay provenance localName
        bundle pkg ->
      Cont compl zero endpoint ->
        Cont endpoint one booleanSource ->
          Cont order localName stoneRead ->
            Cont booleanSource provenance regularRead ->
              Cont stoneRead regularRead publicRead ->
                PkgSig bundle provenance pkg ->
                  PkgSig bundle publicRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row join ∨ hsame row meet ∨ hsame row compl ∨
                            hsame row zero ∨ hsame row one ∨ hsame row order ∨
                              hsame row publicRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont endpoint one booleanSource ∧
                            Cont order localName stoneRead ∧
                              Cont booleanSource provenance regularRead ∧
                                Cont stoneRead regularRead publicRead ∧
                                  PkgSig bundle publicRead pkg)
                        hsame ∧
                      UnaryHistory endpoint ∧ UnaryHistory booleanSource ∧
                        UnaryHistory stoneRead ∧ UnaryHistory regularRead ∧
                          UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BooleanAlgebraCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows complZero endpointOne orderLocalName booleanProvenance
    stoneRegular provenancePkg publicPkg
  obtain ⟨joinUnary, meetUnary, complUnary, zeroUnary, oneUnary, orderUnary,
    _transportUnary, _replayUnary, provenanceUnary, localNameUnary, _joinMeetOrder,
    _complZeroReplay, _transportReplayProvenance, _carrierProvenancePkg,
    _carrierLocalNamePkg⟩ := carrierRows
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed complUnary zeroUnary complZero
  have booleanSourceUnary : UnaryHistory booleanSource :=
    unary_cont_closed endpointUnary oneUnary endpointOne
  have stoneReadUnary : UnaryHistory stoneRead :=
    unary_cont_closed orderUnary localNameUnary orderLocalName
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed booleanSourceUnary provenanceUnary booleanProvenance
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed stoneReadUnary regularReadUnary stoneRegular
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
              hsame row one ∨ hsame row order ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont endpoint one booleanSource ∧
              Cont order localName stoneRead ∧ Cont booleanSource provenance regularRead ∧
                Cont stoneRead regularRead publicRead ∧ PkgSig bundle publicRead pkg)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointOne, orderLocalName, booleanProvenance, stoneRegular,
          publicPkg⟩
  }
  exact
    ⟨cert, endpointUnary, booleanSourceUnary, stoneReadUnary, regularReadUnary,
      publicReadUnary⟩

end BEDC.Derived.BooleanalgebraUp
