import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ArzelaAscoliUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ArzelaAscoliPacket [AskSetup] [PackageSetup]
    (source target family probes equicont image modulus selections _transport _route provenance
      _nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory family ∧ UnaryHistory probes ∧
    UnaryHistory equicont ∧ UnaryHistory image ∧ UnaryHistory modulus ∧
      UnaryHistory selections ∧ Cont source probes family ∧ Cont probes equicont modulus ∧
        Cont image selections provenance ∧ PkgSig bundle provenance pkg

theorem ArzelaAscoliPacket_equicontinuity_net_handoff [AskSetup] [PackageSetup]
    {source target family probes equicont image modulus selections transport route provenance
      nameCert finiteHandoff targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArzelaAscoliPacket source target family probes equicont image modulus selections transport
        route provenance nameCert bundle pkg →
      Cont probes equicont finiteHandoff →
        Cont image selections targetRead →
          PkgSig bundle finiteHandoff pkg →
            PkgSig bundle targetRead pkg →
              UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory probes ∧
                UnaryHistory equicont ∧ UnaryHistory image ∧ UnaryHistory finiteHandoff ∧
                  UnaryHistory targetRead ∧ Cont probes equicont finiteHandoff ∧
                    Cont image selections targetRead ∧ PkgSig bundle finiteHandoff pkg ∧
                      PkgSig bundle targetRead pkg := by
  intro packet finiteRow targetRow finitePkg targetPkg
  obtain ⟨sourceUnary, targetUnary, _familyUnary, probesUnary, equicontUnary, imageUnary,
    _modulusUnary, selectionsUnary, _familyRow, _modulusRow, _provenanceRow,
    _packetPkg⟩ := packet
  have finiteUnary : UnaryHistory finiteHandoff :=
    unary_cont_closed probesUnary equicontUnary finiteRow
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed imageUnary selectionsUnary targetRow
  exact
    ⟨sourceUnary, targetUnary, probesUnary, equicontUnary, imageUnary, finiteUnary,
      targetReadUnary, finiteRow, targetRow, finitePkg, targetPkg⟩

end BEDC.Derived.ArzelaAscoliUp
