function canSee(seq, i, j) {
  const x1 = Math.min(i, j);
  const x2 = Math.max(i, j);
  const y1 = seq[x1];
  const y2 = seq[x2];
  const dx = x2 - x1;
  const dy = y2 - y1;

  for (let k = x1 + 1; k < x2; k++) {
    if ((seq[k] - y1) * dx > dy * (k - x1)) {
      return false;
    }
  }
  return true;
}

function isValidBidirectionalSequence(seq) {
  const n = seq.length;

  for (let i = 0; i < n; i++) {
    let visibleCount = 0;
    for (let j = 0; j < n; j++) {
      if (i === j) continue;
      if (canSee(seq, i, j)) {
        visibleCount++;
      }
    }
    const k = seq[i];
    if (visibleCount !== k) {
      console.log({ i, k, visibleCount });
      return false;
    }
  }

  return true;
}
