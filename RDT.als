open util/ordering[Time]

sig Time {}

abstract sig Packet{
	checksum: Checksum one -> Time,
	seqnum: SequenceNumber one -> Time
}
one sig DataPacket extends Packet{
	data: Data one -> Time
}

one sig ConfirmationPacket extends Packet{
	confirmation: Confirmation one -> Time
}

abstract sig Confirmation {
	checksum: Checksum
}

one sig Ack extends Confirmation{} 

sig Data {
	checksum: Checksum
}

abstract sig SequenceNumber {}

one sig Sequence0, Sequence1 extends SequenceNumber {}

abstract sig Checksum{}

sig DataChecksum extends Checksum {
	data: Data
}

one sig AckChecksum extends Checksum {
	confirmation: Confirmation
}

one sig Channel{
	packet: Packet -> Time
}

abstract sig State{}

one sig Waiting, Sending extends State{}

abstract sig Computer {
  buffer: Data -> Time,
  state: State -> Time,
  currentSeq: SequenceNumber -> Time
}

one sig Sender extends Computer {
	sent: SequenceNumber -> Data lone -> Time
}
one sig Receiver extends Computer{
	response: ConfirmationPacket lone -> Time
}

fact CheckChecksum{
	all d : Data |
		d.checksum.data = d
	Ack.checksum = AckChecksum
	AckChecksum.confirmation = Ack
}


pred Init[s, r : Computer, c: Channel, t : Time] {
  s.state.t = Sending
  r.state.t = Waiting
  no s.sent[SequenceNumber].t
  no r.response.t
  no c.packet.t
  s.buffer.t = Data
  no r.buffer.t
  s.currentSeq.t = Sequence0
  r.currentSeq.t = Sequence0
}

pred Success[s, r : Computer, c : Channel, t : Time] {
  no s.buffer.t 
  r.buffer.t = Data
  no c.packet.t
  no s.sent[s.currentSeq.t].t
  no r.response.t
}


pred Transition[s, r : Computer, c : Channel, t, t' : Time] {
  SenderAddToChannel[s,r,c,t,t'] or 
  SenderTakeOutOfChannel[s,r,c,t,t'] or 
  ReceiverAddToChannel[s,r,c,t,t'] or
  ReceiverTakeOutOfChannel[s,r,c,t,t'] or
  MalformData[s,r,c,t,t']
}

pred SenderAddToChannel[s,r : Computer, c : Channel, t, t' : Time] {
	s.state.t = Sending
	s.state.t' = Waiting
	r.state.t = Waiting
	r.state.t' = Waiting
	r.buffer.t' = r.buffer.t
	no r.response.t
	no r.response.t'
	no c.packet.t
	c.packet.t' = DataPacket
	c.packet.t'.checksum.t' = s.sent[(s.currentSeq.t')].t'.checksum
	c.packet.t'.seqnum.t' = (s.currentSeq.t)
	s.currentSeq.t' = (s.currentSeq.t)
	r.currentSeq.t' = r.currentSeq.t
	s.sent[(SequenceNumber - s.currentSeq.t)].t' = s.sent[(SequenceNumber - s.currentSeq.t)].t
	let p = DataPacket | (
	  (not no s.sent[(s.currentSeq.t)].t) =>(
		p.data.t' = s.sent[(s.currentSeq.t)].t and
		s.sent[(s.currentSeq.t)].t' = s.sent[(s.currentSeq.t)].t and
		s.buffer.t' = s.buffer.t
	  )
	  else(
		one d : s.buffer.t | 
		  p.data.t' = d and
		  s.buffer.t' = s.buffer.t - d and
		  s.sent[(s.currentSeq.t)].t' = d
	  )
	)
}

pred SenderTakeOutOfChannel[s,r : Computer, c : Channel, t, t' : Time] {
	s.state.t = Waiting
	s.state.t' = Sending
	r.state.t = Waiting
	r.state.t' = Waiting
	s.buffer.t' = s.buffer.t
	r.buffer.t' = r.buffer.t
	not no c.packet.t
	c.packet.t in ConfirmationPacket
	no c.packet.t'
	no r.response.t
	no r.response.t'
	r.currentSeq.t' = r.currentSeq.t
	let p = c.packet.t |
	  (p.checksum.t = AckChecksum and p.seqnum.t = s.currentSeq.t) => (
		s.currentSeq.t' = (SequenceNumber - s.currentSeq.t) and
		no s.sent[s.currentSeq.t'].t' and
		s.sent[s.currentSeq.t].t' = s.sent[s.currentSeq.t].t
	  ) else (
		s.currentSeq.t' = s.currentSeq.t and
		no s.sent[(SequenceNumber - s.currentSeq.t)].t' and
		s.sent[s.currentSeq.t'].t' = s.sent[s.currentSeq.t].t
	  )
}

pred ReceiverTakeOutOfChannel[s,r : Computer, c : Channel, t, t' : Time] {
	s.state.t = Waiting
	s.state.t' = Waiting
	r.state.t = Waiting
	r.state.t' = Sending
	s.buffer.t' = s.buffer.t
	s.sent.t' = s.sent.t
	not no c.packet.t
	c.packet.t in DataPacket
	no c.packet.t'
	no r.response.t
	not no r.response.t'
	s.currentSeq.t' = s.currentSeq.t
	one p: c.packet.t |
	// not malformed
	  (p.data.t.checksum = p.checksum.t and p.seqnum.t = r.currentSeq.t) =>(
		r.buffer.t' = r.buffer.t + p.data.t and
		r.response.t'.confirmation.t' = Ack and
		r.response.t'.seqnum.t' = r.currentSeq.t and
		r.response.t'.checksum.t' = AckChecksum and
		r.currentSeq.t' = (SequenceNumber - r.currentSeq.t)
	  )
		// malformed
		else (
			r.buffer.t' = r.buffer.t and
			r.response.t'.confirmation.t' = Ack and
			r.response.t'.seqnum.t' = (SequenceNumber - r.currentSeq.t) and
			r.response.t'.checksum.t' = AckChecksum and
			r.currentSeq.t' = r.currentSeq.t
		)
}

pred ReceiverAddToChannel[s,r : Computer, c : Channel, t, t' : Time]{
	s.state.t = Waiting
	s.state.t' = Waiting
	r.state.t = Sending
	r.state.t' = Waiting
	r.currentSeq.t' = r.currentSeq.t
	s.currentSeq.t' = s.currentSeq.t
	s.buffer.t' = s.buffer.t
	r.buffer.t' = r.buffer.t
	s.sent.t' = s.sent.t
	not no r.response.t
	no r.response.t'
	c.packet.t' = r.response.t
	c.packet.t'.seqnum.t' = r.response.t.seqnum.t
	c.packet.t'.confirmation.t' = r.response.t.confirmation.t
	c.packet.t'.checksum.t' = r.response.t.checksum.t
	c.packet.t.checksum.t = c.packet.t.confirmation.t.checksum
}

pred MalformData[s,r : Computer, c : Channel, t, t' : Time]{
	not no c.packet.t
	s.state.t' = s.state.t
	r.state.t' = r.state.t
	s.sent.t' = s.sent.t
	r.response.t' = r.response.t
	s.buffer.t' = s.buffer.t
	r.buffer.t' = r.buffer.t
	c.packet.t' = c.packet.t
	c.packet.t'.checksum.t' = c.packet.t.checksum.t
	c.packet.t'.seqnum.t' = c.packet.t.seqnum.t
	s.currentSeq.t' = s.currentSeq.t
	r.currentSeq.t' = r.currentSeq.t
	(c.packet.t in DataPacket) =>
	(
		// malforming a Data packet
		c.packet.t.checksum.t = c.packet.t.data.t.checksum and
		let originalData = c.packet.t.data.t |
			c.packet.t'.data.t' in (Data - originalData)
	) else (
		// malforming an Ack/Nak packet
		c.packet.t.checksum.t = c.packet.t.confirmation.t.checksum and
		c.packet.t'.confirmation.t' = (Confirmation - c.packet.t.confirmation.t)
	)
}

fact Trace {
  let s = Sender |
    let r = Receiver |
		let c = Channel |
      Init[s, r, c, first] and
      all t: Time - last | 
        let t' = t.next | 
          Transition[s, r, c, t, t'] or (
            Success[s, r, c, t'] and 
            Success[s, r, c, t]
          )
}

pred ShowTrace {}

run ShowTrace for exactly 3 Data, 5 Checksum, 10 Time

pred Unsuccessful[] {
  	no Sender.buffer.last 
  	not Receiver.buffer.last = Data
  	no Channel.packet.last
  	no Sender.sent.last
  	no Receiver.response.last
}

pred Successful[] {
	Success[Sender, Receiver, Channel, last]
}

run Unsuccessful for exactly 3 Data, 5 Checksum, 100 Time

run Successful for exactly 3 Data, 5 Checksum, 13 Time
