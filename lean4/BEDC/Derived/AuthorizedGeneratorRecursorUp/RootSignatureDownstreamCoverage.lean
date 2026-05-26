import BEDC.Derived.AuthorizedGeneratorRecursorUp.RootOutputNameCertSaturation
import BEDC.Derived.AuthorizedGeneratorRecursorUp.RootSignatureRowTotality

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootSignatureDownstreamCoverage [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N rootRead auditRead boundaryRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I E rootRead ->
        Cont O A auditRead ->
          Cont G N boundaryRead ->
            Cont O C publicRead ->
              PkgSig bundle boundaryRead pkg ->
                PkgSig bundle publicRead pkg ->
                  UnaryHistory rootRead ∧ UnaryHistory auditRead ∧
                    UnaryHistory boundaryRead ∧ UnaryHistory publicRead ∧
                      SemanticNameCert
                        (fun row : BHist =>
                          AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N
                            bundle pkg ∧ hsame row publicRead)
                        (fun row : BHist => hsame row publicRead ∧ Cont O C publicRead)
                        (fun row : BHist =>
                          hsame row publicRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle publicRead pkg)
                        hsame ∧
                        hsame H (append A C) ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier rootRoute auditRoute boundaryRoute publicRoute boundaryPkg publicPkg
  have rootRows :=
    AuthorizedGeneratorRecursorRootSignatureRowTotality carrier rootRoute auditRoute
      boundaryRoute boundaryPkg
  have outputRows :=
    AuthorizedGeneratorRecursorRootOutputNameCertSaturation carrier publicRoute boundaryRoute
      publicPkg
  rcases rootRows with ⟨_rootCert, rootUnary, auditUnary, boundaryUnary⟩
  rcases outputRows with
    ⟨publicCert, publicUnary, _boundaryUnary, _publicRoute, _boundaryRoute, _publicPkg⟩
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, _unaryO, _unaryA, _unaryH,
      _unaryC, _unaryP, _unaryG, _unaryN, _rootCarrier, _descentCarrier,
      _outputCarrier, transportSame, provenancePkg⟩
  exact ⟨rootUnary, auditUnary, boundaryUnary, publicUnary, publicCert, transportSame,
    provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
