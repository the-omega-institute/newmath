import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EquicontinuityFamilyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EquicontinuityFamilyPacket [AskSetup] [PackageSetup]
    (source target family probes equicont image modulus selections _transport _route provenance
      _nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory family ∧ UnaryHistory probes ∧
    UnaryHistory equicont ∧ UnaryHistory image ∧ UnaryHistory modulus ∧
      UnaryHistory selections ∧ Cont source target family ∧ Cont probes equicont modulus ∧
        Cont image selections provenance ∧ PkgSig bundle provenance pkg

theorem EquicontinuityFamilyPacket_namecert_obligations [AskSetup] [PackageSetup]
    {source target family probes equicont image modulus selections transport route provenance
      nameCert finiteHandoff toleranceRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityFamilyPacket source target family probes equicont image modulus selections
        transport route provenance nameCert bundle pkg ->
      Cont probes equicont finiteHandoff ->
        Cont modulus selections toleranceRead ->
          Cont finiteHandoff toleranceRead ledgerRead ->
            PkgSig bundle ledgerRead pkg ->
              UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory family ∧
                UnaryHistory probes ∧ UnaryHistory equicont ∧ UnaryHistory modulus ∧
                  UnaryHistory finiteHandoff ∧ UnaryHistory toleranceRead ∧
                    UnaryHistory ledgerRead ∧ Cont probes equicont finiteHandoff ∧
                      Cont modulus selections toleranceRead ∧
                        Cont finiteHandoff toleranceRead ledgerRead ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle ledgerRead pkg := by
  intro packet finiteRow toleranceRow ledgerRow ledgerPkg
  obtain ⟨sourceUnary, targetUnary, familyUnary, probesUnary, equicontUnary, _imageUnary,
    modulusUnary, selectionsUnary, _familyRow, _modulusRow, _provenanceRow,
    provenancePkg⟩ := packet
  have finiteUnary : UnaryHistory finiteHandoff :=
    unary_cont_closed probesUnary equicontUnary finiteRow
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed modulusUnary selectionsUnary toleranceRow
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed finiteUnary toleranceUnary ledgerRow
  exact
    ⟨sourceUnary, targetUnary, familyUnary, probesUnary, equicontUnary, modulusUnary,
      finiteUnary, toleranceUnary, ledgerUnary, finiteRow, toleranceRow, ledgerRow,
      provenancePkg, ledgerPkg⟩

end BEDC.Derived.EquicontinuityFamilyUp
