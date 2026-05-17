import BEDC.Derived.UniformCauchyCriterionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_real_completion_finite_envelope_namecert_obligations
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name realRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont tail sealRow realRead →
        Cont realRead transports completionRead →
          PkgSig bundle realRead pkg →
            PkgSig bundle completionRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow
                        transports routes provenance name bundle pkg ∧
                      hsame row completionRead)
                  (fun row : BHist =>
                    hsame row completionRead ∧ UnaryHistory row ∧
                      Cont realRead transports completionRead)
                  (fun row : BHist =>
                    PkgSig bundle name pkg ∧ PkgSig bundle realRead pkg ∧
                      PkgSig bundle completionRead pkg ∧ hsame row completionRead)
                  hsame ∧
                UnaryHistory windows ∧ UnaryHistory tolerance ∧ UnaryHistory tail ∧
                  UnaryHistory realRead ∧ UnaryHistory completionRead ∧
                    Cont modulus tolerance tail ∧ Cont tail sealRow realRead ∧
                      Cont realRead transports completionRead ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle realRead pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro packet tailSealRealRead realReadTransportsCompletion realReadPkg completionReadPkg
  have packetSource :
      UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports
        routes provenance name bundle pkg :=
    packet
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRealRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed realReadUnary transportsUnary realReadTransportsCompletion
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow
                transports routes provenance name bundle pkg ∧
              hsame row completionRead)
          (fun row : BHist =>
            hsame row completionRead ∧ UnaryHistory row ∧
              Cont realRead transports completionRead)
          (fun row : BHist =>
            PkgSig bundle name pkg ∧ PkgSig bundle realRead pkg ∧
              PkgSig bundle completionRead pkg ∧ hsame row completionRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro completionRead ⟨packetSource, hsame_refl completionRead⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport completionReadUnary (hsame_symm source.right),
            realReadTransportsCompletion⟩
      ledger_sound := by
        intro _row source
        exact ⟨namePkg, realReadPkg, completionReadPkg, source.right⟩
    }
  exact
    ⟨cert, windowsUnary, toleranceUnary, tailUnary, realReadUnary, completionReadUnary,
      modulusToleranceTail, tailSealRealRead, realReadTransportsCompletion, namePkg,
      realReadPkg, completionReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
