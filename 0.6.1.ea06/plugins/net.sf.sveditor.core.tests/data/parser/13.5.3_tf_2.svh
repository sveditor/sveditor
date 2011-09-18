module m;
	logic a, w;
	task t1 (output o = a) ; // default binds to m.a
	// ...
	endtask :t1
	task t2 (output o = b) ; // illegal, b cannot be resolved
	// ...
	endtask :t2
	task t3 (inout io = w) ; // default binds to m.w
	// ...
	endtask :t1
endmodule :m

module n;
	logic a;
	initial begin
		m.t1(); // same as m.t1(m.a), not m.t1(n.a);
		// at end of task, value of t1.o is copied to m.a
		m.t3(); // same as m.t3(m.w)
		// value of m.w is copied to t3.io at start of task and
		// value of t3.io is copied to m.w at end of task
	end
endmodule :n

