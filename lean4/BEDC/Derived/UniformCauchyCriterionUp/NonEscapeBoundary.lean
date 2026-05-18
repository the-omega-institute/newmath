import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_non_escape_boundary [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name sealRead
      publicRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont tail sealRow sealRead ->
        Cont transports routes publicRead ->
          PkgSig bundle publicRead pkg ->
            UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
              UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                UnaryHistory sealRead ∧ UnaryHistory publicRead ∧
                  Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                    Cont tail sealRow sealRead ∧ Cont transports routes publicRead ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg ∧
                        (Cont publicRead (BHist.e0 hostTail) sealRead -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet tailSealRead transportsRoutesPublic publicPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed transportsUnary routesUnary transportsRoutesPublic
  have sameTransportsSealRead : hsame transports sealRead :=
    cont_deterministic tailSealRowTransports tailSealRead
  have sealReadRoutesPublic : Cont sealRead routes publicRead :=
    cont_hsame_transport sameTransportsSealRead (hsame_refl routes) (hsame_refl publicRead)
      transportsRoutesPublic
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      sealReadUnary, publicReadUnary, indexWindowsModulus, modulusToleranceTail,
      tailSealRead, transportsRoutesPublic, namePkg, publicPkg,
      fun backToSeal =>
        cont_mutual_extension_right_tail_absurd.left sealReadRoutesPublic backToSeal⟩

end BEDC.Derived.UniformCauchyCriterionUp
