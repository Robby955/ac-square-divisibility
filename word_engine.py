"""Independent ordinary rank-two interpreter, extracted from the proof source."""

def integers(value):
    if not isinstance(value, list) or any(type(x) is not int for x in value):
        raise ValueError("expected integer array, excluding booleans")
    return value


def words(value):
    if not isinstance(value, list) or len(value) != 2:
        raise ValueError("expected exactly two relators")
    for word in value:
        if any(x not in (1, -1, 2, -2) for x in integers(word)):
            raise ValueError("letter outside rank-two alphabet")
    return value


def moves(value):
    if any(not 0 <= x < 14 for x in integers(value)):
        raise ValueError("move outside ordinary frozen table")
    return value


def reduce_word(word):
    output = []
    for letter in word:
        if output and output[-1] == -letter:
            output.pop()
        else:
            output.append(letter)
    return output


def apply_move(state, move):
    """Pure rank-two replay for validating the already frozen intermediate trace."""
    words(state)
    moves([move])
    result = [list(word) for word in state]
    if move < 2:
        result[move] = [-letter for letter in reversed(result[move])]
    elif move < 6:
        target = (move - 2) // 2
        other = result[1 - target]
        if move % 2:
            other = [-letter for letter in reversed(other)]
        result[target] = reduce_word(result[target] + other)
    else:
        target, index = divmod(move - 6, 4)
        letter = (1, -1, 2, -2)[index]
        result[target] = reduce_word([letter] + result[target] + [-letter])
    return result


def primitive_cost(ids):
    return sum(3 if mid in (3, 5) else 1 for mid in moves(ids))
