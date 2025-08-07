#define N 2

byte next_ticket = 0;
byte curr_ticket = 0;
byte my_ticket[N];
bool in_cs[N];

proctype worker(byte id) {
  d_step {
    my_ticket[id] = next_ticket;
    next_ticket++;
  }

  do
  :: curr_ticket == my_ticket[id] -> break;
  od

  in_cs[id] = true;
  skip; // simulate work
  in_cs[id] = false;

  d_step {
    curr_ticket++;
  }
}

ltl safety { [](!(in_cs[0] && in_cs[1])) }

ltl liveness0 { []((my_ticket[0] < curr_ticket) -> <>in_cs[0]) }
ltl liveness1 { []((my_ticket[1] < curr_ticket) -> <>in_cs[1]) }

init {
  atomic {
    run worker(0);
    run worker(1);
  }
}