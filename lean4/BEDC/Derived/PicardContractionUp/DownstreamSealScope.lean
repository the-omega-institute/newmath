import BEDC.Derived.PicardContractionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_downstream_seal_scope [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      odeConsumer newtonConsumer regRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates endpoint odeConsumer ->
        Cont iterates endpoint newtonConsumer ->
          Cont iterates modulus regRead ->
            Cont regRead endpoint realRead ->
              PkgSig bundle odeConsumer pkg ->
                PkgSig bundle newtonConsumer pkg ->
                  PkgSig bundle realRead pkg ->
                    SemanticNameCert
                        (fun row : BHist =>
                          hsame row odeConsumer ∨ hsame row newtonConsumer ∨
                            hsame row realRead)
                        (fun _row : BHist =>
                          Cont iterates endpoint odeConsumer ∧
                            Cont iterates endpoint newtonConsumer ∧
                              Cont regRead endpoint realRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧
                            (PkgSig bundle odeConsumer pkg ∨
                              PkgSig bundle newtonConsumer pkg ∨
                                PkgSig bundle realRead pkg))
                        hsame ∧
                      UnaryHistory odeConsumer ∧ UnaryHistory newtonConsumer ∧
                        UnaryHistory regRead ∧ UnaryHistory realRead ∧
                          PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet iteratesEndpointOde iteratesEndpointNewton iteratesModulusReg
    regEndpointReal odePkg newtonPkg realPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have odeUnary : UnaryHistory odeConsumer :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointOde
  have newtonUnary : UnaryHistory newtonConsumer :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointNewton
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusReg
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regUnary endpointUnary regEndpointReal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row odeConsumer ∨ hsame row newtonConsumer ∨ hsame row realRead)
          (fun _row : BHist =>
            Cont iterates endpoint odeConsumer ∧ Cont iterates endpoint newtonConsumer ∧
              Cont regRead endpoint realRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              (PkgSig bundle odeConsumer pkg ∨ PkgSig bundle newtonConsumer pkg ∨
                PkgSig bundle realRead pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro odeConsumer (Or.inl (hsame_refl odeConsumer))
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
        cases source with
        | inl sameOde =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameOde)
        | inr rest =>
            cases rest with
            | inl sameNewton =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameNewton))
            | inr sameReal =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameReal))
    }
    pattern_sound := by
      intro _row _source
      exact ⟨iteratesEndpointOde, iteratesEndpointNewton, regEndpointReal⟩
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameOde =>
          exact ⟨unary_transport odeUnary (hsame_symm sameOde), Or.inl odePkg⟩
      | inr rest =>
          cases rest with
          | inl sameNewton =>
              exact
                ⟨unary_transport newtonUnary (hsame_symm sameNewton),
                  Or.inr (Or.inl newtonPkg)⟩
          | inr sameReal =>
              exact
                ⟨unary_transport realUnary (hsame_symm sameReal),
                  Or.inr (Or.inr realPkg)⟩
  }
  exact ⟨cert, odeUnary, newtonUnary, regUnary, realUnary, namePkg⟩

end BEDC.Derived.PicardContractionUp
