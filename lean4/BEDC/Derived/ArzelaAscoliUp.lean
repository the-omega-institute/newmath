import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ArzelaAscoliUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ArzelaAscoliPacket [AskSetup] [PackageSetup]
    (source target family probes equicont image modulus bundleSelect transport route provenance
      nameCert endpoint : BHist)
    (probeBundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory family ∧ UnaryHistory probes ∧
    UnaryHistory equicont ∧ UnaryHistory image ∧ UnaryHistory modulus ∧
      UnaryHistory bundleSelect ∧ UnaryHistory transport ∧ UnaryHistory route ∧
        UnaryHistory provenance ∧ UnaryHistory nameCert ∧ UnaryHistory endpoint ∧
          Cont source probes equicont ∧ Cont family image modulus ∧
            Cont equicont modulus endpoint ∧ Cont transport route provenance ∧
              PkgSig probeBundle provenance pkg

theorem ArzelaAscoliPacket_namecert_obligations [AskSetup] [PackageSetup]
    {source target family probes equicont image modulus bundleSelect transport route provenance
      nameCert endpoint : BHist}
    {probeBundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArzelaAscoliPacket source target family probes equicont image modulus bundleSelect transport
        route provenance nameCert endpoint probeBundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          ArzelaAscoliPacket source target family probes equicont image modulus bundleSelect
            transport route provenance nameCert endpoint probeBundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          ArzelaAscoliPacket source target family probes equicont image modulus bundleSelect
            transport route provenance nameCert endpoint probeBundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          ArzelaAscoliPacket source target family probes equicont image modulus bundleSelect
            transport route provenance nameCert endpoint probeBundle pkg ∧ hsame row endpoint)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.ArzelaAscoliUp
