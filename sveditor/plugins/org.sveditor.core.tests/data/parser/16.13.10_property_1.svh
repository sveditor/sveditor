module m;
	// if the clock ticks once more, then a shall be true at the next clock tick
	property p1;
		nexttime a;
	endproperty
	// the clock shall tick once more and a shall be true at the next clock tick.
	property p2;
		s_nexttime a;
	endproperty
	// as long as the clock ticks, a shall be true at each future clock tick
	// starting from the next clock tick	
	property p3;
		nexttime always a;
	endproperty
	// the clock shall tick at least once more and as long as it ticks, a shall
	// be true at every clock tick starting from the next one
	property p4;
		s_nexttime always a;
	endproperty
	// if the clock ticks at least once more, it shall tick enough times for a to
	// be true at some point in the future starting from the next clock tick
	property p5;
		nexttime s_eventually a;
	endproperty
	// a shall be true sometime in the strict future
	property p6;
		s_nexttime s_eventually a;
	endproperty
	// if there are at least two more clock ticks, a shall be true at the second
	// future clock tick
	property p7;
		nexttime[2] a;
	endproperty
	// there shall be at least two more clock ticks, and a shall be true at the
	// second future clock tick
	property p8;
		s_nexttime[2] a;
	endproperty	
	
endmodule