import BEDC.Derived.EquicontinuityFamilyUp.TasteGate
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

theorem EquicontinuityFamilyPacket_shared_center_coverage [AskSetup] [PackageSetup]
    {source target family probes equicont image modulus selections transport route provenance
      nameCert finiteRead familyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityFamilyPacket source target family probes equicont image modulus selections
        transport route provenance nameCert bundle pkg ->
      Cont probes equicont finiteRead ->
        Cont finiteRead modulus familyRead ->
          PkgSig bundle familyRead pkg ->
            UnaryHistory probes ∧ UnaryHistory equicont ∧ UnaryHistory modulus ∧
              UnaryHistory finiteRead ∧ UnaryHistory familyRead ∧
                Cont probes equicont finiteRead ∧ Cont finiteRead modulus familyRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle familyRead pkg := by
  intro packet finiteRow familyRow familyPkg
  obtain ⟨_sourceUnary, _targetUnary, _familyUnary, probesUnary, equicontUnary, _imageUnary,
    modulusUnary, _selectionsUnary, _familyLedger, _modulusLedger, _provenanceLedger,
    provenancePkg⟩ := packet
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed probesUnary equicontUnary finiteRow
  have familyReadUnary : UnaryHistory familyRead :=
    unary_cont_closed finiteUnary modulusUnary familyRow
  exact
    ⟨probesUnary, equicontUnary, modulusUnary, finiteUnary, familyReadUnary, finiteRow,
      familyRow, provenancePkg, familyPkg⟩

theorem EquicontinuityFamilyPacket_rational_radius_transport [AskSetup] [PackageSetup]
    {source target family probes equicont image modulus selections transport route provenance
      nameCert toleranceRead radiusRead centerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityFamilyPacket source target family probes equicont image modulus selections
        transport route provenance nameCert bundle pkg →
      Cont modulus selections toleranceRead →
        Cont probes equicont centerRead →
          Cont centerRead toleranceRead radiusRead →
            PkgSig bundle radiusRead pkg →
              UnaryHistory toleranceRead ∧ UnaryHistory centerRead ∧
                UnaryHistory radiusRead ∧ Cont modulus selections toleranceRead ∧
                  Cont probes equicont centerRead ∧ Cont centerRead toleranceRead radiusRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle radiusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet toleranceRow centerRow radiusRow radiusPkg
  obtain ⟨_sourceUnary, _targetUnary, _familyUnary, probesUnary, equicontUnary, _imageUnary,
    modulusUnary, selectionsUnary, _familyRow, _modulusRow, _provenanceRow,
    provenancePkg⟩ := packet
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed modulusUnary selectionsUnary toleranceRow
  have centerUnary : UnaryHistory centerRead :=
    unary_cont_closed probesUnary equicontUnary centerRow
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed centerUnary toleranceUnary radiusRow
  exact
    ⟨toleranceUnary, centerUnary, radiusUnary, toleranceRow, centerRow, radiusRow,
      provenancePkg, radiusPkg⟩

theorem EquicontinuityFamilyPacket_ledger_non_escape_package [AskSetup] [PackageSetup]
    {source target family probes equicont image modulus selections transport route provenance
      nameCert finiteRead toleranceRead ledgerRead radiusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityFamilyPacket source target family probes equicont image modulus selections
        transport route provenance nameCert bundle pkg →
      Cont probes equicont finiteRead →
        Cont modulus selections toleranceRead →
          Cont finiteRead toleranceRead ledgerRead →
            Cont ledgerRead modulus radiusRead →
              PkgSig bundle radiusRead pkg →
                UnaryHistory finiteRead ∧ UnaryHistory toleranceRead ∧
                  UnaryHistory ledgerRead ∧ UnaryHistory radiusRead ∧
                    Cont probes equicont finiteRead ∧ Cont modulus selections toleranceRead ∧
                      Cont finiteRead toleranceRead ledgerRead ∧
                        Cont ledgerRead modulus radiusRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle radiusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet finiteRow toleranceRow ledgerRow radiusRow radiusPkg
  obtain ⟨_sourceUnary, _targetUnary, _familyUnary, probesUnary, equicontUnary, _imageUnary,
    modulusUnary, selectionsUnary, _familyRow, _modulusRow, _provenanceRow,
    provenancePkg⟩ := packet
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed probesUnary equicontUnary finiteRow
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed modulusUnary selectionsUnary toleranceRow
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed finiteUnary toleranceUnary ledgerRow
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed ledgerUnary modulusUnary radiusRow
  exact
    ⟨finiteUnary, toleranceUnary, ledgerUnary, radiusUnary, finiteRow, toleranceRow,
      ledgerRow, radiusRow, provenancePkg, radiusPkg⟩

end BEDC.Derived.EquicontinuityFamilyUp
