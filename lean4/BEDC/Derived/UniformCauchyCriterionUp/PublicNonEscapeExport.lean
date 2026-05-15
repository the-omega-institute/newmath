import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_public_non_escape_export [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      realRead publicRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail tailRead ->
        Cont tail sealRow realRead ->
          Cont tailRead realRead publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                  UnaryHistory tailRead ∧ UnaryHistory realRead ∧ UnaryHistory publicRead ∧
                    Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                      Cont index tail tailRead ∧ Cont tail sealRow realRead ∧
                        Cont tailRead realRead publicRead ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle publicRead pkg ∧
                            (Cont publicRead (BHist.e0 hostTail) tailRead -> False) ∧
                              (Cont publicRead (BHist.e1 hostTail) realRead -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRead tailSealReal tailRealPublic publicPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed tailReadUnary realReadUnary tailRealPublic
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      tailReadUnary, realReadUnary, publicReadUnary, indexWindowsModulus, modulusToleranceTail,
      indexTailRead, tailSealReal, tailRealPublic, namePkg, publicPkg,
      (fun backToTail =>
        cont_mutual_extension_right_tail_absurd.left tailRealPublic backToTail),
      (fun backToReal =>
        let realTailPublic : Cont realRead tailRead publicRead :=
          cont_result_hsame_transport
            (cont_intro (h := realRead) (k := tailRead) rfl)
            (hsame_symm
              (unary_cont_comm tailReadUnary realReadUnary tailRealPublic
                (cont_intro (h := realRead) (k := tailRead) rfl)))
        cont_mutual_extension_right_tail_absurd.right realTailPublic backToReal)⟩

end BEDC.Derived.UniformCauchyCriterionUp
