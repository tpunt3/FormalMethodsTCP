open util/ordering[Time]

sig Time {}

abstract sig Packet{}
one sig DataPacket extends Packet{
	data: Data one -> Time,
	checksum: Checksum one-> Time
}
abstract sig ConfirmationPacket extends Packet{}
one sig AckPacket, NakPacket extends ConfirmationPacket{} 

sig Data {
	checksum: Checksum
}

sig Checksum{
	data: Data
}

one sig Channel{
	packet: Packet->Time
}

abstract sig State{}

one sig Waiting, Sending extends State{}

abstract sig Computer {
  buffer: Data->Time,
  state: State -> Time
}

one sig Sender extends Computer {
	sent: Data lone-> Time
}
one sig Receiver extends Computer{
	response: ConfirmationPacket lone -> Time
}

fact CheckChecksum{
	all d : Data |
		d.checksum.data = d
}


pred Init[s, r : Computer, c: Channel, t : Time] {
  s.state.t = Sending
  r.state.t = Waiting
  no s.sent.t
  no r.response.t
  no c.packet.t
  s.buffer.t = Data
  no r.buffer.t
}

pred Success[s, r : Computer, c : Channel, t : Time] {
  no s.buffer.t 
  r.buffer.t = Data
  no c.packet.t
  no s.sent.t
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
	let p = DataPacket | (
	  (not no s.sent.t) =>(
		p.data.t' = s.sent.t and
		s.sent.t' = s.sent.t and
		s.buffer.t' = s.buffer.t
	  )
	  else(
	    one d : s.buffer.t | 
		  p.data.t' = d and
		  s.buffer.t' = s.buffer.t - d and
		  s.sent.t' = d
	  ) and
	  c.packet.t' = p and
	  c.packet.t'.checksum.t' = s.sent.t'.checksum
           )
}

pred SenderTakeOutOfChannel[s,r : Computer, c : Channel, t, t' : Time] {
	s.state.t = Waiting
	s.state.t' = Sending
	r.state.t = Waiting
	r.state.t' = Waiting
	s.buffer.t' = s.buffer.t
	r.buffer.t' = r.buffer.t
	c.packet.t'.checksum.t' = c.packet.t.checksum.t
	not no c.packet.t
	c.packet.t in ConfirmationPacket
	no c.packet.t'
	no r.response.t
	no r.response.t'
	one p: c.packet.t |
	  (p = AckPacket) => (
	    no s.sent.t'
	  ) else (
	    s.sent.t' = s.sent.t
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
	one p: c.packet.t |
	  (p.data.t.checksum = p.checksum.t) =>(
	         r.buffer.t' = r.buffer.t + p.data.t and
		r.response.t' = AckPacket
	  ) 
		else(
		  r.buffer.t' = r.buffer.t and
		  r.response.t' = NakPacket
		)
}

pred ReceiverAddToChannel[s,r : Computer, c : Channel, t, t' : Time]{
	s.state.t = Waiting
	s.state.t' = Waiting
	r.state.t = Sending
	r.state.t' = Waiting
	s.buffer.t' = s.buffer.t
	r.buffer.t' = r.buffer.t
	s.sent.t' = s.sent.t
	not no r.response.t
	no r.response.t'
	c.packet.t' = r.response.t
}

pred MalformData[s,r : Computer, c : Channel, t, t' : Time]{
	not no c.packet.t
	c.packet.t in DataPacket
	s.state.t' = s.state.t
	r.state.t' = r.state.t
	s.sent.t' = s.sent.t
	r.response.t' = r.response.t
	s.buffer.t' = s.buffer.t
	r.buffer.t' = r.buffer.t
	c.packet.t.checksum.t = c.packet.t.data.t.checksum
	c.packet.t'.checksum.t' = c.packet.t.checksum.t
	let originalData = c.packet.t.data.t |
		c.packet.t'.data.t' in (Data - originalData)
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

run ShowTrace for exactly 3 Data, 3 Checksum, 30 Time

pred Unsuccessful[] {
  not Success[Sender, Receiver, Channel, last]
}

pred Successful[] {
	Success[Sender, Receiver, Channel, last]
}

run Unsuccessful for exactly 3 Data, 3 Checksum, 25 Time

run Successful for exactly 3 Data, 3 Checksum, 13 Time
