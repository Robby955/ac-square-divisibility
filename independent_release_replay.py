"""Independent signed-letter replay; imports no construction or official verifier code."""
def replay(initial, moves):
    """A separate local interpreter; no constructor/reduction routine is imported."""
    def reduced(w):
        out = []
        for a in w:
            if out and out[-1] == -a: out.pop()
            else: out.append(a)
        return out
    def inverse(w): return [-a for a in reversed(w)]
    state = [list(w) for w in initial]
    peak = work = sum(map(len, state))
    for mid in moves:
        if type(mid) is not int or not 0 <= mid < 14: raise ValueError('invalid move')
        if mid < 2: state[mid] = inverse(state[mid])
        elif mid < 6:
            i = (mid-2)//2; w = state[1-i]
            state[i] = reduced(state[i] + (inverse(w) if mid % 2 else w))
        else:
            i, j = divmod(mid-6,4); a = (1,-1,2,-2)[j]
            state[i] = reduced([a]+state[i]+[-a])
        length = sum(map(len,state)); work += length; peak = max(peak,length)
    return state, peak, work
