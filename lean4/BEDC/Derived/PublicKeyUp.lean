import BEDC.FKernel.NameCert

namespace BEDC.Derived.PublicKeyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def PKCertifiedEnc
    (Pub Msg Ciph : BHist -> Prop)
    (PKEncrypt : BHist -> BHist -> BHist -> Prop)
    (pk m c : BHist) : Prop :=
  Pub pk ∧ Msg m ∧ Ciph c ∧ PKEncrypt pk m c

def PublicKeyCertifiedEnc
    (Msg Pub Ciph : BHist -> Prop)
    (PKEncrypt : BHist -> BHist -> BHist -> Prop)
    (pk m c : BHist) : Prop :=
  Pub pk ∧ Msg m ∧ Ciph c ∧ PKEncrypt pk m c

def PKDecryptEncryptExact
    (MsgClassifier : BHist -> BHist -> Prop)
    (PKKeyGen : BHist -> BHist -> Prop)
    (Pub Msg Ciph : BHist -> Prop)
    (PKEncrypt PKDecrypt : BHist -> BHist -> BHist -> Prop) : Prop :=
  forall {pk sk m c : BHist},
    PKKeyGen pk sk ->
      PKCertifiedEnc Pub Msg Ciph PKEncrypt pk m c ->
        exists d : BHist, PKDecrypt sk c d ∧ MsgClassifier d m

theorem PublicKey_decrypt_encrypt_correctness
    {Msg Pub Ciph : BHist -> Prop}
    {MsgClassifier : BHist -> BHist -> Prop}
    {PKKeyGen : BHist -> BHist -> Prop}
    {PKEncrypt PKDecrypt : BHist -> BHist -> BHist -> Prop}
    (msgCert : SemanticNameCert Msg Msg Msg MsgClassifier)
    (exactness :
      PKDecryptEncryptExact MsgClassifier PKKeyGen Pub Msg Ciph PKEncrypt PKDecrypt)
    {pk sk m c : BHist} :
    PKKeyGen pk sk ->
      PKCertifiedEnc Pub Msg Ciph PKEncrypt pk m c ->
        exists d : BHist, Msg d ∧ PKDecrypt sk c d ∧ MsgClassifier d m := by
  intro keyGenerated certifiedEncryption
  have msgM : Msg m := certifiedEncryption.right.left
  cases exactness keyGenerated certifiedEncryption with
  | intro d decrypted =>
      have classifiedMD : MsgClassifier m d :=
        NameCert.equiv_symm msgCert.core decrypted.right
      have msgD : Msg d :=
        NameCert.carrier_respects_equiv msgCert.core classifiedMD msgM
      exact Exists.intro d (And.intro msgD decrypted)

def PublicKeyDecryptEncryptExact
    (Msg : BHist -> Prop)
    (MsgRel : BHist -> BHist -> Prop)
    (Pub Ciph : BHist -> Prop)
    (PKKeyGen : BHist -> BHist -> Prop)
    (PKEncrypt PKDecrypt : BHist -> BHist -> BHist -> Prop) : Prop :=
  forall pk sk m c : BHist,
    PKKeyGen pk sk ->
      PublicKeyCertifiedEnc Msg Pub Ciph PKEncrypt pk m c ->
        exists d : BHist, PKDecrypt sk c d ∧ MsgRel d m

theorem PublicKeyDecryptEncrypt_correctness
    {Msg Pub Ciph : BHist -> Prop}
    {MsgRel : BHist -> BHist -> Prop}
    {PKKeyGen : BHist -> BHist -> Prop}
    {PKEncrypt PKDecrypt : BHist -> BHist -> BHist -> Prop}
    (msgCert : SemanticNameCert Msg Msg Msg MsgRel)
    (exactness :
      PublicKeyDecryptEncryptExact Msg MsgRel Pub Ciph PKKeyGen PKEncrypt PKDecrypt)
    {pk sk m c : BHist} :
    PKKeyGen pk sk ->
      PublicKeyCertifiedEnc Msg Pub Ciph PKEncrypt pk m c ->
        exists d : BHist, Msg d ∧ PKDecrypt sk c d ∧ MsgRel d m := by
  intro keypair certified
  have decryptWitness := exactness pk sk m c keypair certified
  cases decryptWitness with
  | intro d decryptRows =>
      have sameMD : MsgRel m d :=
        msgCert.core.equiv_symm decryptRows.right
      have msgD : Msg d :=
        msgCert.core.carrier_respects_equiv sameMD certified.right.left
      exact Exists.intro d
        (And.intro msgD (And.intro decryptRows.left decryptRows.right))

end BEDC.Derived.PublicKeyUp
