import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_completion_real_correspondence [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name windowRead
      tailRead sealRead terminalRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows windowRead ->
        Cont windowRead tail tailRead ->
          Cont tail sealRow sealRead ->
            Cont tailRead sealRead terminalRead ->
              Cont terminalRead routes completionRead ->
                PkgSig bundle terminalRead pkg ->
                  PkgSig bundle completionRead pkg ->
                    UnaryHistory windowRead ∧ UnaryHistory tailRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory terminalRead ∧
                        UnaryHistory completionRead ∧ Cont index windows windowRead ∧
                          Cont windowRead tail tailRead ∧ Cont tail sealRow sealRead ∧
                            Cont tailRead sealRead terminalRead ∧
                              Cont terminalRead routes completionRead ∧
                                PkgSig bundle name pkg ∧ PkgSig bundle terminalRead pkg ∧
                                  PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexWindowsWindow windowTail tailSeal terminalRoute terminalCompletion
    terminalPkg completionPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsWindow
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed windowReadUnary tailUnary windowTail
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSeal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed tailReadUnary sealReadUnary terminalRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed terminalReadUnary routesUnary terminalCompletion
  exact
    ⟨windowReadUnary, tailReadUnary, sealReadUnary, terminalReadUnary, completionReadUnary,
      indexWindowsWindow, windowTail, tailSeal, terminalRoute, terminalCompletion, namePkg,
      terminalPkg, completionPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
