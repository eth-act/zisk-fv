`SEGMENT_LAST * (value[i] - segment_last_value[i]) === 0` is the seam that hands
the last row's memory value of one segment to the next segment as an air value.
Deleting it lets the two segments disagree about the value at the boundary, which
is exactly the cross-segment memory continuity the proof has to rely on.
