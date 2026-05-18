import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionTerminalFourFaceWindowExactness [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name windowRead
      regseqRead dyadicRead realSealRead budgetRead exactBoundaryRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index windows windowRead →
        Cont tail sealRow regseqRead →
          Cont windowRead regseqRead dyadicRead →
            Cont dyadicRead sealRow realSealRead →
              Cont realSealRead provenance budgetRead →
                Cont budgetRead name exactBoundaryRead →
                  Cont exactBoundaryRead tail terminalRead →
                    PkgSig bundle terminalRead pkg →
                      UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                        UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                          UnaryHistory windowRead ∧ UnaryHistory regseqRead ∧
                            UnaryHistory dyadicRead ∧ UnaryHistory realSealRead ∧
                              UnaryHistory budgetRead ∧ UnaryHistory exactBoundaryRead ∧
                                UnaryHistory terminalRead ∧ Cont index windows windowRead ∧
                                  Cont tail sealRow regseqRead ∧
                                    Cont windowRead regseqRead dyadicRead ∧
                                      Cont dyadicRead sealRow realSealRead ∧
                                        Cont realSealRead provenance budgetRead ∧
                                          Cont budgetRead name exactBoundaryRead ∧
                                            Cont exactBoundaryRead tail terminalRead ∧
                                              PkgSig bundle name pkg ∧
                                                PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexWindowRead tailSealRegseq windowRegseqDyadic dyadicSealReal
    realProvenanceBudget budgetNameBoundary boundaryTailTerminal terminalPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, provenanceUnary, nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowRead
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRegseq
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowReadUnary regseqReadUnary windowRegseqDyadic
  have realSealReadUnary : UnaryHistory realSealRead :=
    unary_cont_closed dyadicReadUnary sealRowUnary dyadicSealReal
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed realSealReadUnary provenanceUnary realProvenanceBudget
  have exactBoundaryReadUnary : UnaryHistory exactBoundaryRead :=
    unary_cont_closed budgetReadUnary nameUnary budgetNameBoundary
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed exactBoundaryReadUnary tailUnary boundaryTailTerminal
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      windowReadUnary, regseqReadUnary, dyadicReadUnary, realSealReadUnary, budgetReadUnary,
      exactBoundaryReadUnary, terminalReadUnary, indexWindowRead, tailSealRegseq,
      windowRegseqDyadic, dyadicSealReal, realProvenanceBudget, budgetNameBoundary,
      boundaryTailTerminal, namePkg, terminalPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
