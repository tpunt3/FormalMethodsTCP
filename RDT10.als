open util/ordering[Time]

sig Time {}

sig Data {}

abstract sig Computer {
  buffer: Data->Time
}

one sig Sender, Receiver extends Computer {}


pred Init[s, r : Computer, t : Time] {
  s.buffer.t = Data
  no r.buffer.t
}

pred Success[s, r : Computer, t : Time] {
  no s.buffer.t
  r.buffer.t = Data
}


pred Transition[s, r : Computer, t, t' : Time] {
  one d: s.buffer.t |
    d + r.buffer.t = r.buffer.t' and
    s.buffer.t' = s.buffer.t - d
}

fact Trace {
  let s = Sender |
    let r = Reveiver | 
      init[Sender, Receiver, first]
      all t: Time - last | 
        let t' = t.next | 
          Transition[s, r, t,t'] or (
            success[s, r, t'] and 
            success[s, r, t]
          )
}

pred ShowTrace {}

run ShowTrace for exactly 10 Data, 30 Time

pred Unsuccessful[] {
  not Success[Sender, Receiver, last]
}

run Unsuccessful for exactly 10 Data, 30 Time
