import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_seal_route_uniqueness [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name sealA sealB :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont tail sealRow sealA →
        Cont tail sealRow sealB →
          PkgSig bundle sealA pkg →
            PkgSig bundle sealB pkg →
              UnaryHistory tail ∧ UnaryHistory sealRow ∧ UnaryHistory sealA ∧
                UnaryHistory sealB ∧ hsame sealA sealB ∧ Cont tail sealRow sealA ∧
                  Cont tail sealRow sealB ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle sealA pkg ∧ PkgSig bundle sealB pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet tailSealA tailSealB sealAPkg sealBPkg
  obtain ⟨_indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have sealAUnary : UnaryHistory sealA :=
    unary_cont_closed tailUnary sealRowUnary tailSealA
  have sealBUnary : UnaryHistory sealB :=
    unary_cont_closed tailUnary sealRowUnary tailSealB
  have sameSeal : hsame sealA sealB :=
    cont_deterministic tailSealA tailSealB
  exact
    ⟨tailUnary, sealRowUnary, sealAUnary, sealBUnary, sameSeal, tailSealA, tailSealB, namePkg,
      sealAPkg, sealBPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
