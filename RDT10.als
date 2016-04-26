open util/ordering[Time]

sig Data{}

abstract sig Computer{buffer: Data->Time}

one sig Sender, Receiver extends Computer{}

sig Time{}

pred init[s, r: Computer, t: Time]{
	s.buffer.t = Data
	no r.buffer.t
}

pred success[s, r: Computer, t: Time]{
	no s.buffer.t 
	r.buffer.t = Data
}


pred Transition[s,r:Computer, t,t':Time]{
	one d: s.buffer.t | d + r.buffer.t = r.buffer.t' and s.buffer.t' = s.buffer.t - d
}

fact Trace{
	init[Sender, Receiver, first]
	all t: Time - last | let t' = t.next | Transition[Sender, Receiver, t,t'] or
	(success[Sender, Receiver, t'] and success[Sender, Receiver, t])
}

pred ShowTrace{}

run ShowTrace for exactly 10 Data, 30 Time

pred unsuccessful[]{
	not success[Sender, Receiver, last]
}

run unsuccessful for exactly 10 Data, 30 Time
