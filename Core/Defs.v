From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
From Heaps
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap coding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition Hash := [ordType of nat].

Record Block {Transaction VProof : eqType} :=
  mkB {
    prevBlockHash : Hash;
    txs : seq Transaction;
    proof : VProof;
  }.

Definition eq_block {T P : eqType} (b b' : @Block T P) :=
  match (b, b') with
  | (mkB p t pf, mkB p' t' pf') =>
    [&& p == p', t == t' & pf == pf']
  end.
      
Lemma eq_blockP {T P : eqType} : Equality.axiom (@eq_block T P).
Proof.
case=> p t pf; case=> p' t' pf'; rewrite /eq_block/=.
case H2: (p == p'); [move/eqP: H2=>?; subst p'| constructor 2];
  last by case=>?; subst p';rewrite eqxx in H2.
case H3: (t == t'); [move/eqP: H3=>?; subst t'| constructor 2];
  last by case=>?; subst t';rewrite eqxx in H3.
case H4: (pf == pf'); [move/eqP: H4=>?; subst pf'| constructor 2];
  last by case=>?; subst pf';rewrite eqxx in H4.
by constructor 1. 
Qed.

Canonical Block_eqMixin {T P : eqType} :=
  Eval hnf in EqMixin (@eq_blockP T P).
Canonical Block_eqType {T P : eqType} :=
  Eval hnf in EqType (@Block T P) (@Block_eqMixin T P).

(* Strict version of the prefix *)
Definition is_strict_prefix {T: eqType} (bc bc' : seq T) :=
  exists b bc1, bc' = bc ++ (b :: bc1).

Notation "'[' bc1 '<<<' bc2 ']'" := (is_strict_prefix bc1 bc2).

Fixpoint sprefixb {T: eqType} (s1 s2 : seq T) :=
  if s2 is y :: s2' then
    if s1 is x :: s1' then (x == y) && (sprefixb s1' s2')
    else true
  else false.

(* Non-strict prefix *)
Definition is_prefix {T :eqType} (bc bc' : seq T) :=
  exists bc1, bc' = bc ++ bc1.

Notation "'[' bc1 '<<=' bc2 ']'" := (is_prefix bc1 bc2).

(* Decidable fork *)
Definition fork {T: eqType} (bc1 bc2 : seq T) :=
  ~~[|| sprefixb bc1 bc2, sprefixb bc2 bc1 | bc1 == bc2].

Definition Address := nat.
Definition Timestamp := nat.

Parameter VProof : eqType.
Parameter Transaction : eqType.

Definition block := @Block Transaction VProof.
Parameter GenesisBlock : block.

Definition Blockchain := seq block.

(* In fact, it's a forrest, as it also keeps orphan blocks *)
Definition BlockTree := union_map Hash block.

Parameter hashT : Transaction -> Hash.
Parameter hashB : block -> Hash.
Parameter genProof : Address -> Blockchain -> option VProof.
Parameter VAF : VProof -> Timestamp -> Blockchain -> bool.
Parameter FCR : Blockchain -> Blockchain -> bool.

(* Transaction pools *)
Definition TxPool := seq Transaction.

(* Transaction is valid and consistent with the given chain *)
Parameter txValid : Transaction -> Blockchain -> bool.
Parameter tpExtend : TxPool -> BlockTree -> Transaction -> TxPool.

Notation "A > B" := (FCR A B).
Notation "A >= B" := (A = B \/ A > B).
Notation "# b" := (hashB b) (at level 20).
Notation "## b" := (hashB b \\-> tt) (at level 80).

Definition bcLast (bc : Blockchain) := last GenesisBlock bc.

Definition subchain (bc1 bc2 : Blockchain) := exists p q, bc2 = p ++ bc1 ++ q.

(* 1.  Genesis block properties *)

Hypothesis init_hash : prevBlockHash GenesisBlock = #GenesisBlock.

Hypothesis init_tx : txs GenesisBlock = [::].

(* 2.  Transaction validation *)

Hypothesis txValid_nil : forall t, txValid t [::]. 

(* 3.  Hashes *)

Hypothesis hashB_inj : injective hashB.

Hypothesis hashT_inj : injective hashT.

(* 4.  VAF *)

(* This axiom seems reasonable: it shouldn't be possible
   to generate a block _from_ the chain it is supposed to tail.  *)
Hypothesis VAF_nocycle :
  forall (b : block) ts (bc : Blockchain), VAF (proof b) ts bc -> b \notin bc.

(* 2. FCR *)

Hypothesis FCR_subchain :
  forall bc1 bc2, subchain bc1 bc2 -> bc2 >= bc1.

Hypothesis FCR_ext :
  forall (bc : Blockchain) (b : block) (ext : seq block),
    bc ++ (b :: ext) > bc.

Hypothesis FCR_rel :
  forall (A B : Blockchain),
    A = B \/ A > B \/ B > A.

Hypothesis FCR_nrefl :
  forall (bc : Blockchain), bc > bc -> False.

Hypothesis FCR_trans :
  forall (A B C : Blockchain), A > B -> B > C -> A > C.

Definition btHasBlock (bt : BlockTree) (b : block) := #b \in dom bt.

Notation "b ∈ bt" := (btHasBlock bt b) (at level 70).
Notation "b ∉ bt" := (~~ btHasBlock bt b) (at level 70).

Definition valid_block b : bool :=
  prevBlockHash b != #b.

Definition has_init_block (bt : BlockTree) :=
  find (# GenesisBlock) bt = Some GenesisBlock.

Definition validH (bt : BlockTree) :=
  forall h b, find h bt = Some b -> h = hashB b.

(* We only add "fresh blocks" *)
Definition btExtend (bt : BlockTree) (b : block) :=
  if #b \in dom bt then bt else #b \\-> b \+ bt.

Definition next_of (bt : BlockTree) b : pred Block :=
  [pred b' | (hashB b == prevBlockHash b') && (hashB b' \in dom bt)].

(* All paths/chains should start with the GenesisBlock *)
Fixpoint compute_chain' (bt : BlockTree) b remaining n : Blockchain :=
  (* Preventing cycles in chains *)
  if (hashB b) \in remaining
  then
    let rest := seq.rem (hashB b) remaining in
    (* Supporting primitive inductions *)
    if n is n'.+1 then
      match find (prevBlockHash b) bt with
      (* No parent *)
      | None => [:: b]
      (* Build chain prefix recursively *)
      | Some prev =>
        rcons (nosimpl (compute_chain' (free (hashB b) bt) prev rest n')) b
      end
    else [::]
  else [::].

(* Compute chain from the block *)
Definition compute_chain bt b :=
  compute_chain' bt b (keys_of bt) (size (keys_of bt)).

(* Total get_block function *)
Definition get_block (bt : BlockTree) k : Block :=
  if find k bt is Some b then b else GenesisBlock.

(* Collect all blocks *)
Definition all_blocks (bt : BlockTree) := [seq get_block bt k | k <- keys_of bt].

Definition is_block_in (bt : BlockTree) b := exists k, find k bt = Some b.

(* All chains from the given tree *)
Definition good_chain (bc : Blockchain) :=
  if bc is h :: _ then h == GenesisBlock else false.

(* Transaction validity *)
Fixpoint tx_valid_chain' (bc prefix : seq block) :=
  if bc is b :: bc'
  then [&& all [pred t | txValid t prefix] (txs b) &
        tx_valid_chain' bc' (rcons prefix b)]
  else true.

Definition tx_valid_chain bc := tx_valid_chain' bc [::].

Definition all_chains bt := [seq compute_chain bt b | b <- all_blocks bt].

Definition good_chains bt := [seq c <- all_chains bt | good_chain c && tx_valid_chain c].

(* Get the blockchain *)
Definition take_better_bc bc2 bc1 :=
  if (good_chain bc2 && tx_valid_chain bc2) && (bc2 > bc1) then bc2 else bc1.

Definition btChain bt : Blockchain :=
  foldr take_better_bc [:: GenesisBlock] (all_chains bt).

Definition tx_valid_block bc (b : block) := all [pred t | txValid t bc] (txs b).

Definition good_bt bt :=
  forall b, b \in all_blocks bt ->
            good_chain (compute_chain bt b) && tx_valid_chain (compute_chain bt b).

(* Implementation of PoS protocol as a STS *)
Definition nid := nat.
Definition peers_t := seq nid.

Inductive Message :=
  | NullMsg
  | AddrMsg of peers_t
  | ConnectMsg 
  | BlockMsg of block
  | TxMsg of Transaction
  | InvMsg of seq Hash
  | GetDataMsg of Hash.

Inductive MessageType :=
  | MNull
  | MAddr
  | MConnect
  | MBlock
  | MTx
  | MInv
  | MGetData.

Definition msg_type (msg : Message) : MessageType :=
  match msg with
  | NullMsg => MNull
  | AddrMsg _ => MAddr
  | ConnectMsg => MConnect
  | BlockMsg _ => MBlock
  | TxMsg _ => MTx
  | InvMsg _ => MInv
  | GetDataMsg _ => MGetData
  end.

Definition msg_block (msg : Message) : block :=
  match msg with
  | BlockMsg b => b
  | _ => GenesisBlock
  end.

Definition msg_hashes (msg : Message) : seq Hash :=
  match msg with
  | InvMsg sh => sh
  | GetDataMsg h => [:: h]
  | _ => [::]
  end.

Definition eq_msg a b :=
 match a, b with
  | NullMsg, NullMsg => true
  | NullMsg, _ => false
  | AddrMsg prsA, AddrMsg prsB => (prsA == prsB)
  | AddrMsg _, _ => false
  | ConnectMsg, ConnectMsg => true
  | ConnectMsg, _ => false
  | BlockMsg bA, BlockMsg bB => (bA == bB)
  | BlockMsg _, _ => false
  | TxMsg tA, TxMsg tB => (tA == tB)
  | TxMsg _, _ => false
  | InvMsg hA, InvMsg hB => (hA == hB)
  | InvMsg _, _ => false
  | GetDataMsg hA, GetDataMsg hB => (hA == hB)
  | GetDataMsg _, _ => false
 end.

Ltac simple_tactic mb n n' B :=
  (case: mb=>//[|n' p'|n'|b'|t'|p' h'|p' h']; do? [by constructor 2];
   case B: (n == n'); [by case/eqP:B=><-; constructor 1|constructor 2];
   case=>E; subst n'; rewrite eqxx in B).

Lemma eq_msgP : Equality.axiom eq_msg.
Proof.
move=> ma mb. rewrite/eq_msg.
case: ma=>[|p||b|t|h|h].
- case: mb=>//[|p'||b'|t'|h'|h']; do? [by constructor 2]; by constructor 1.
- case: mb=>//[|p'||b'|t'|h'|h']; do? [by constructor 2].
  case B: ((p == p')).
  - by move/eqP:B=><-; constructor 1.
  by constructor 2; case=>Z; subst p'; rewrite eqxx in B.
- case:mb=>////[|p'||b'|t'|h'|h']; do? [by constructor 2|by constructor 1].
- case:mb=>////[|p'||b'|t'|h'|h']; do? [by constructor 2].
  case B: (b == b'); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst b'; rewrite eqxx in B.
- case:mb=>////[|p'||b'|t'|h'|h']; do? [by constructor 2].
  case B: (t == t'); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst t'; rewrite eqxx in B.
- case:mb=>////[|p'||b'|t'|h'|h']; do? [by constructor 2].
  case B: (h == h'); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst h'; rewrite eqxx in B.
- case:mb=>////[|p'||b'|t'|h'|h']; do? [by constructor 2].
  case B: (h == h'); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst h'; rewrite eqxx in B.
Qed.

Canonical Msg_eqMixin := Eval hnf in EqMixin eq_msgP.
Canonical Msg_eqType := Eval hnf in EqType Message Msg_eqMixin.

Record Packet := mkP {src: nid; dst: nid; msg: Message}.
Definition NullPacket := mkP 0 0 NullMsg.

Definition eq_pkt a b :=
  ((src a) == (src b)) && ((dst a) == (dst b)) && ((msg a) == (msg b)).

Lemma eq_pktP : Equality.axiom eq_pkt.
Proof.
case=>sa da ma [sb] db mb; rewrite/eq_pkt/=.
case P1: (sa == sb)=>/=; last by constructor 2; case=>/eqP; rewrite P1.
case P2: (da == db)=>/=; last by constructor 2; case=> _ /eqP; rewrite P2.
case P3: (ma == mb)=>/=; last by constructor 2; case=> _ _ /eqP; rewrite P3.
by constructor 1; move/eqP: P1=><-; move/eqP: P2=><-; move/eqP: P3=><-.
Qed.

Canonical Packet_eqMixin := Eval hnf in EqMixin eq_pktP.
Canonical Packet_eqType := Eval hnf in EqType Packet Packet_eqMixin.

Record State :=
  Node {
    id : nid;
    peers : peers_t;
    blockTree : BlockTree;
    txPool : TxPool;
  }.

Definition Init (n : nid) : State :=
  Node n [:: n] (#GenesisBlock \\-> GenesisBlock) [::].

Definition ToSend := seq Packet.
Definition emitZero : ToSend := [:: NullPacket].
Definition emitOne (packet : Packet) : ToSend := [:: packet].
Definition emitMany (packets : ToSend) := packets.

Definition emitBroadcast (from : nid) (dst : seq nid) (msg : Message) :=
  [seq (mkP from to msg) | to <- dst].

Definition procMsg (st: State) (from : nid) (msg: Message) (ts: Timestamp) :=
    let: (Node n prs bt pool) := st in
    match msg with
    | ConnectMsg =>
      let: ownHashes := (keys_of bt) ++ [seq hashT t | t <- pool] in
      pair (Node n (undup (from :: prs)) bt pool)
           (emitOne(mkP n from (InvMsg ownHashes))) 

    | AddrMsg knownPeers =>
      let: newP := [seq x <- knownPeers | x \notin prs] in
      let: connects := [seq mkP n p ConnectMsg | p <- newP] in
      let: updP := undup (prs ++ newP) in
      pair (Node n updP bt pool)
           (emitMany(connects) ++ emitBroadcast n prs (AddrMsg updP))

    | BlockMsg b =>
      let: newBt := (btExtend bt b) in
      let: newPool := [seq t <- pool | txValid t (btChain newBt)] in
      let: ownHashes := (keys_of newBt) ++ [seq hashT t | t <- newPool] in
      pair (Node n prs newBt newPool) (emitBroadcast n prs (InvMsg ownHashes))

    | TxMsg tx =>
      let: newPool := tpExtend pool bt tx in
      let: ownHashes := (keys_of bt) ++ [seq hashT t | t <- newPool] in
      pair (Node n prs bt newPool) (emitBroadcast n prs (InvMsg ownHashes))

    | InvMsg peerHashes =>
      let: ownHashes := (keys_of bt) ++ [seq hashT t | t <- pool] in
      let: newH := [seq h <- peerHashes | h \notin ownHashes] in
      let: gets := [seq mkP n from (GetDataMsg h) | h <- newH] in
      pair st (emitMany(gets))

    | GetDataMsg h =>
      (* Do not respond to yourself *)
      if from == n then pair st emitZero else
      let: matchingBlocks := [:: get_block bt h] in
      let: matchingTxs := [seq t <- pool | (hashT t) == h] in
      match ohead matchingBlocks with
      | Some(b) =>
        pair (Node n prs bt pool) (emitOne(mkP n from (BlockMsg b)))
      | _ =>
        match ohead matchingTxs with
        | Some (tx) =>
          pair (Node n prs bt pool) (emitOne(mkP n from (TxMsg tx)))
        | _ => pair st emitZero
        end
      end

    | NullMsg => pair st emitZero
    end.

Inductive InternalTransition :=
  | TxT of Transaction
  | MintT.

Definition procInt (st : State) (tr : InternalTransition) (ts : Timestamp) :=
    let: (Node n prs bt pool) := st in
    match tr with
    | TxT tx => pair st (emitBroadcast n prs (TxMsg tx))

    (* Assumption: nodes broadcast to themselves as well! => simplifies logic *)
    | MintT =>
      let: bc := (btChain bt) in
      let: attempt := genProof n bc in
      match attempt with
      | Some(pf) =>
          if VAF pf ts bc then
            let: allowedTxs := [seq t <- pool | txValid t bc] in
            let: prevBlock := (last GenesisBlock bc) in
            let: block := mkB (hashB prevBlock) allowedTxs pf in

            if tx_valid_block (btChain bt) block then
              let: newBt := (btExtend bt block) in
              let: newPool := [seq t <- pool | txValid t (btChain newBt)] in
              let: ownHashes := (keys_of newBt) ++ [seq hashT t | t <- newPool] in
              pair (Node n prs newBt newPool) (emitBroadcast n prs (BlockMsg block))
            else
              pair st emitZero

          else
            pair st emitZero

      | _ => pair st emitZero
      end
    end.

Definition StateMap := union_map [ordType of nid] State.

Fixpoint initState n : StateMap :=
  if n is n'.+1 then (n \\-> Init n) \+ (initState n') else Unit.

Definition PacketSoup := seq Packet.

Record World :=
  mkW {
    localState : StateMap;
    inFlightMsgs : PacketSoup;
    consumedMsgs : PacketSoup;
  }.

Definition holds (n : nid) (w : World) (cond : State -> Prop) :=
  forall (st : State),
    find n (localState w) = Some st -> cond st.

Definition Coh (w : World) :=
  [/\ valid (localState w),
     forall (n : nid),
       holds n w (fun st => id st == n),
     forall (n : nid),
       holds n w (fun st => valid (blockTree st)),
     forall (n : nid),
       holds n w (fun st => validH (blockTree st)),
     forall (n : nid),
       holds n w (fun st => has_init_block (blockTree st)) &
     forall (n : nid),
       holds n w (fun st => uniq (peers st))
  ].

Record Qualifier := Q { ts: Timestamp; allowed: nid; }.

Inductive system_step (w w' : World) (q : Qualifier) : Prop :=
| Idle of Coh w /\ w = w'
| Deliver (p : Packet) (st : State) of
      Coh w & (dst p) = allowed q &
      p \in inFlightMsgs w &
      find (dst p) (localState w) = Some st &
      let: (st', ms) := procMsg st (src p) (msg p) (ts q) in
      w' = mkW (upd (dst p) st' (localState w))
               (seq.rem p (inFlightMsgs w) ++ ms)
               (rcons (consumedMsgs w) p)
| Intern (proc : nid) (t : InternalTransition) (st : State) of
      Coh w & proc = allowed q &
      find proc (localState w) = Some st &
      let: (st', ms) := (procInt st t (ts q)) in
      w' = mkW (upd proc st' (localState w))
               (ms ++ (inFlightMsgs w))
               (consumedMsgs w).

Definition Schedule := seq Qualifier.

Fixpoint reachable' (s : Schedule) (w w' : World) : Prop :=
  if s is (ins :: insts)
  then exists via, reachable' insts w via /\ system_step via w' ins
  else w = w'.

Definition reachable (w w' : World) :=
  exists s, reachable' s w w'.

Definition initWorld N := mkW (initState N) [::] [::].
