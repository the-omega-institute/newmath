import BEDC.Derived.RegSeqRatUp.CommonTailWindow

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegSeqRatCommonTailTerminalSectionCover [AskSetup] [PackageSetup]
    {source tail0 tail1 commonWindow endpoint radius regularity classifier0 classifier1
      classifierCommon realSeal transport route provenance cert terminalRead coverRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatCommonTailWindowPacket source tail0 tail1 commonWindow endpoint radius
        regularity classifier0 classifier1 classifierCommon realSeal transport route
        provenance cert bundle pkg ->
      Cont realSeal cert terminalRead ->
        Cont terminalRead route coverRead ->
          PkgSig bundle terminalRead pkg ->
            PkgSig bundle coverRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row coverRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row commonWindow ∨ hsame row endpoint ∨
                      hsame row radius ∨ hsame row regularity ∨ hsame row realSeal ∨
                        hsame row terminalRead ∨ hsame row coverRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont commonWindow realSeal transport ∧
                      Cont classifierCommon realSeal route ∧
                        Cont realSeal cert terminalRead ∧
                          Cont terminalRead route coverRead ∧ PkgSig bundle coverRead pkg)
                  hsame ∧ UnaryHistory terminalRead ∧ UnaryHistory coverRead := by
  -- BEDC touchpoint anchor: RegSeqRatCommonTailWindowPacket BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet terminalRoute coverRoute _terminalPkg coverPkg
  obtain ⟨carrier0, _carrier1, _classifierFrom0, _classifierFrom1, commonWindowUnary,
    realSealUnary, _transportUnary, routeUnary, certUnary, _sameClassifier0,
    _sameClassifier1, commonWindowRoute, classifierSealRoute, _certPkg⟩ := packet
  obtain ⟨sourceUnary, _tail0Unary, endpointUnary, radiusUnary, regularityUnary,
    _provenanceUnary, _classifier0Unary, _sourceTailEndpoint, _endpointRadiusRegularity,
    _regularityProvenanceClassifier, _classifierPkg⟩ := carrier0
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed realSealUnary certUnary terminalRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed terminalUnary routeUnary coverRoute
  have certCover :
      SemanticNameCert
          (fun row : BHist => hsame row coverRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row commonWindow ∨ hsame row endpoint ∨
              hsame row radius ∨ hsame row regularity ∨ hsame row realSeal ∨
                hsame row terminalRead ∨ hsame row coverRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont commonWindow realSeal transport ∧
              Cont classifierCommon realSeal route ∧ Cont realSeal cert terminalRead ∧
                Cont terminalRead route coverRead ∧ PkgSig bundle coverRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro coverRead ⟨hsame_refl coverRead, coverUnary⟩
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
        intro _row _other sameRows sourceSpec
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceSpec.left,
            unary_transport sourceSpec.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceSpec
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sourceSpec.left))))))
    ledger_sound := by
      intro _row sourceSpec
      exact
        ⟨sourceSpec.right, commonWindowRoute, classifierSealRoute, terminalRoute,
          coverRoute, coverPkg⟩
  }
  exact ⟨certCover, terminalUnary, coverUnary⟩

end BEDC.Derived.RegSeqRatUp
