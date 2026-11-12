(function () {
  "use strict";

  var MAX_N = 16;
  var DEFAULT_ARR = [8, 3, 2, 9, 7, 1, 5, 4];

  var arr = [];
  var nodes = [];
  var root = null;
  var D = 0;
  var steps = [];
  var totalCmp = 0;
  var cur = 0;
  var timer = null;
  var mode = "level";
  var G = {};

  var $ = function (id) {
    return document.getElementById(id);
  };
  var fmt = function (v) {
    return "[" + v.join(", ") + "]";
  };

  function buildTree(a) {
    nodes = [];
    function make(lo, hi, depth, parent) {
      var n = {
        id: nodes.length,
        lo: lo,
        hi: hi,
        depth: depth,
        parent: parent,
        vals: a.slice(lo, hi + 1),
        size: hi - lo + 1,
        left: null,
        right: null,
        leaf: lo === hi,
        mid: null,
        sorted: null,
      };
      nodes.push(n);
      if (lo < hi) {
        n.mid = (lo + hi) >> 1;
        n.left = make(lo, n.mid, depth + 1, n);
        n.right = make(n.mid + 1, hi, depth + 1, n);
      }
      return n;
    }
    root = make(0, a.length - 1, 0, null);
    D = 0;
    nodes.forEach(function (n) {
      if (n.depth > D) D = n.depth;
    });
  }

  function genSteps() {
    steps = [];
    var cmp = 0;
    function push(s) {
      s.cmp = cmp;
      steps.push(s);
      return s;
    }

    nodes.forEach(function (n) {
      n.sorted = n.leaf ? n.vals.slice() : null;
    });

    push({
      kind: "start",
      line: [1],
      active: root.id,
      show: [root.id],
      text:
        "We start with A = " +
        fmt(arr) +
        " and call MERGE-SORT(A, 0, " +
        (arr.length - 1) +
        ").",
    });

    function divide(n) {
      push({
        kind: "divide",
        line: [2, 3, 4, 5],
        active: n.id,
        split: [n.id],
        show: [n.left.id, n.right.id],
        text:
          "MERGE-SORT(A, " +
          n.lo +
          ", " +
          n.hi +
          "): p &lt; r, so find the middle q = ⌊(" +
          n.lo +
          " + " +
          n.hi +
          ") / 2⌋ = " +
          n.mid +
          ". Split " +
          fmt(n.vals) +
          " into " +
          fmt(n.left.vals) +
          " and " +
          fmt(n.right.vals) +
          ".",
      });
    }

    function base(n) {
      push({
        kind: "base",
        line: [2, 7],
        active: n.id,
        base: [n.id],
        merged: [n.id],
        text:
          fmt(n.vals) +
          " has a single element (p = r), so it is already sorted. The recursion stops here.",
      });
    }

    function merge(n) {
      var A = n.left,
        B = n.right,
        L = A.sorted,
        R = B.sorted;
      var out = [],
        i = 0,
        j = 0;
      function payload(kind, extra) {
        var p = {
          nodeId: n.id,
          leftId: A.id,
          rightId: B.id,
          L: L,
          R: R,
          out: out.slice(),
          li: i,
          rj: j,
          kind: kind,
          take: null,
          copySide: null,
        };
        if (extra) {
          for (var k in extra) {
            p[k] = extra[k];
          }
        }
        return p;
      }

      push({
        kind: "merge-start",
        line: [6],
        active: n.id,
        mstart: [n.id],
        merge: payload("start"),
        text:
          "MERGE(A, " +
          n.lo +
          ", " +
          n.mid +
          ", " +
          n.hi +
          "): merge the sorted halves " +
          fmt(L) +
          " and " +
          fmt(R) +
          " into one sorted array.",
      });

      while (i < L.length && j < R.length) {
        cmp++;
        var a = L[i],
          b = R[j];
        var takeL = a <= b;
        out.push(takeL ? a : b);
        push({
          kind: "compare",
          line: [6],
          active: n.id,
          merge: payload("compare", { take: takeL ? "L" : "R" }),
          text:
            a === b
              ? "Compare " +
                a +
                " and " +
                b +
                " → they are equal, so take the left one first (this keeps Merge Sort stable)."
              : "Compare " +
                a +
                " and " +
                b +
                " → " +
                Math.min(a, b) +
                " is smaller, take " +
                Math.min(a, b) +
                ".",
        });
        if (takeL) {
          i++;
        } else {
          j++;
        }
      }

      var side = i < L.length ? "L" : "R";
      var rest = side === "L" ? L.slice(i) : R.slice(j);
      rest.forEach(function (v) {
        out.push(v);
      });
      push({
        kind: "copy",
        line: [6],
        active: n.id,
        merge: payload("copy", { copySide: side }),
        text:
          "The " +
          (side === "L" ? "right" : "left") +
          " half is finished, so the rest " +
          fmt(rest) +
          " of the " +
          (side === "L" ? "left" : "right") +
          " half is copied as it is.",
      });

      n.sorted = out.slice();
      push({
        kind: "merge-done",
        line: [6],
        active: n.id,
        merged: [n.id],
        merge: payload("done", { li: L.length, rj: R.length }),
        text: "Merged result: " + fmt(out) + ".",
      });
    }

    if (mode === "level") {
      var d;
      for (d = 0; d <= D; d++) {
        nodes
          .filter(function (n) {
            return n.depth === d;
          })
          .forEach(function (n) {
            if (n.leaf) {
              base(n);
            } else {
              divide(n);
            }
          });
      }
      for (d = D - 1; d >= 0; d--) {
        nodes
          .filter(function (n) {
            return n.depth === d && !n.leaf;
          })
          .forEach(merge);
      }
    } else {
      (function rec(n) {
        if (n.leaf) {
          base(n);
          return;
        }
        divide(n);
        rec(n.left);
        rec(n.right);
        merge(n);
      })(root);
    }

    push({
      kind: "done",
      line: [7],
      active: null,
      text:
        "Finished! Sorted array: " +
        fmt(root.sorted) +
        " after " +
        cmp +
        " comparison" +
        (cmp === 1 ? "" : "s") +
        ".",
    });
    totalCmp = cmp;
  }

  function stateAt(k) {
    var st = {
      shown: {},
      split: {},
      base: {},
      merged: {},
      mstart: {},
      fresh: {},
      S: steps[k],
    };
    for (var s = 0; s <= k; s++) {
      var S = steps[s];
      (S.show || []).forEach(function (id) {
        st.shown[id] = 1;
        if (s === k) {
          st.fresh[id] = 1;
        }
      });
      (S.split || []).forEach(function (id) {
        st.split[id] = 1;
      });
      (S.base || []).forEach(function (id) {
        st.base[id] = 1;
        if (s === k) {
          st.fresh[id] = 1;
        }
      });
      (S.merged || []).forEach(function (id) {
        st.merged[id] = 1;
        if (s === k) {
          st.fresh[id] = 1;
        }
      });
      (S.mstart || []).forEach(function (id) {
        st.mstart[id] = 1;
      });
    }
    return st;
  }

  function srcCls(m, side) {
    var vals = side === "L" ? m.L : m.R;
    var idx = side === "L" ? m.li : m.rj;
    return vals.map(function (_, t) {
      if (m.kind === "done") {
        return "used";
      }
      if (t < idx) {
        return "used";
      }
      if (m.kind === "compare" && t === idx) {
        return m.take === side ? "taken" : "cmp";
      }
      if (m.kind === "copy" && m.copySide === side) {
        return "taken";
      }
      return "";
    });
  }

  function layout() {
    var maxLen = 1;
    arr.forEach(function (v) {
      maxLen = Math.max(maxLen, String(v).length);
    });
    G.cw = Math.max(36, maxLen * 11 + 16);
    G.bh = 40;
    G.rowH = 78;
    G.padL = 112;
    G.padT = 14;
    var splitDepth = {};
    nodes.forEach(function (n) {
      if (!n.leaf) {
        splitDepth[n.mid + 1] = n.depth;
      }
    });
    G.pos = [0];
    for (var i = 1; i < arr.length; i++) {
      G.pos[i] = G.pos[i - 1] + G.cw + 12 + (D - splitDepth[i]) * 9;
    }
    G.W = G.padL + G.pos[arr.length - 1] + G.cw + 16;
    G.H = G.padT + 2 * D * G.rowH + G.bh + 16;
  }
  function cx(n) {
    return G.padL + (G.pos[n.lo] + G.pos[n.hi] + G.cw) / 2;
  }
  function yRow(r) {
    return G.padT + r * G.rowH;
  }
  function mergeRow(n) {
    return 2 * D - n.depth;
  }

  function boxSVG(c, y, vals, cls, cells) {
    var w = vals.length * G.cw,
      x0 = c - w / 2;
    var s = '<g class="box ' + cls.join(" ") + '">';
    vals.forEach(function (v, t) {
      s +=
        '<rect class="cell ' +
        ((cells && cells[t]) || "") +
        '" x="' +
        (x0 + t * G.cw) +
        '" y="' +
        y +
        '" width="' +
        G.cw +
        '" height="' +
        G.bh +
        '" rx="3"/>';
      if (v !== null && v !== undefined) {
        s +=
          '<text x="' +
          (x0 + t * G.cw + G.cw / 2) +
          '" y="' +
          (y + G.bh / 2) +
          '" dy=".35em">' +
          v +
          "</text>";
      }
    });
    return s + "</g>";
  }
  function ghostSVG(c, y, count) {
    var w = count * G.cw;
    return (
      '<rect class="ghostbox" x="' +
      (c - w / 2) +
      '" y="' +
      y +
      '" width="' +
      w +
      '" height="' +
      G.bh +
      '" rx="4"/>'
    );
  }
  function lineSVG(x1, y1, x2, y2, cls, arrow) {
    return (
      '<line class="edge ' +
      cls +
      '" x1="' +
      x1 +
      '" y1="' +
      y1 +
      '" x2="' +
      x2 +
      '" y2="' +
      y2 +
      '"' +
      (arrow ? ' marker-end="url(#' + arrow + ')"' : "") +
      "/>"
    );
  }

  function renderTree(st) {
    var m = st.S.merge || null;
    var live = m && m.kind !== "done" ? m : null;
    var s =
      "<defs>" +
      '<marker id="am" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path class="arrow-m" d="M0,0 L10,5 L0,10 z"/></marker>' +
      '<marker id="ag" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path class="arrow-g" d="M0,0 L10,5 L0,10 z"/></marker>' +
      "</defs>";

    var r, d;
    for (r = 0; r <= 2 * D; r++) {
      var label;
      if (r <= D) {
        label = r === 0 ? "Level 0 (Split)" : "Level " + r;
      } else {
        d = 2 * D - r;
        label = r === D + 1 ? "Conquer (Merge)" : "Level " + d;
      }
      s +=
        '<text class="rowlabel" x="4" y="' +
        (yRow(r) + G.bh / 2) +
        '" dy=".35em">' +
        label +
        "</text>";
    }
    if (D > 0) {
      var sy = yRow(D) + G.bh + (G.rowH - G.bh) / 2;
      s +=
        '<line class="sep" x1="0" y1="' +
        sy +
        '" x2="' +
        G.W +
        '" y2="' +
        sy +
        '"/>';
    }

    nodes.forEach(function (n) {
      if (n.leaf) {
        if (n.depth < D && st.merged[n.id]) {
          s += lineSVG(
            cx(n),
            yRow(n.depth) + G.bh,
            cx(n),
            yRow(mergeRow(n)) - 3,
            "leafcopy",
            "",
          );
        }
        return;
      }
      [n.left, n.right].forEach(function (c) {
        var onD = !!st.split[n.id];
        s += lineSVG(
          cx(n),
          yRow(n.depth) + G.bh,
          cx(c),
          yRow(c.depth) - 3,
          onD ? "" : "ghost",
          onD ? "am" : "",
        );
        var onM = !!st.mstart[n.id];
        s += lineSVG(
          cx(c),
          yRow(mergeRow(c)) + G.bh,
          cx(n),
          yRow(mergeRow(n)) - 3,
          onM ? "merge" : "ghost",
          onM ? "ag" : "",
        );
      });
    });

    nodes.forEach(function (n) {
      var deepLeaf = n.leaf && n.depth === D;
      var side = live
        ? live.leftId === n.id
          ? "L"
          : live.rightId === n.id
            ? "R"
            : null
        : null;
      var fresh = st.fresh[n.id] ? ["fresh"] : [];
      var c = cx(n),
        y = yRow(n.depth);

      if (st.shown[n.id]) {
        var cls = ["div"].concat(fresh);
        if (n.leaf && st.base[n.id]) {
          cls.push("is-leaf");
        }
        if (
          st.S.active === n.id &&
          (st.S.kind === "divide" ||
            st.S.kind === "start" ||
            st.S.kind === "base")
        ) {
          cls.push("is-active");
        }
        var cells = null;
        if (deepLeaf && side) {
          cls.push("is-src");
          cells = srcCls(live, side);
        }
        s += boxSVG(c, y, n.vals, cls, cells);
      } else {
        s += ghostSVG(c, y, n.size);
      }

      if (!deepLeaf) {
        var my = yRow(mergeRow(n));
        if (st.merged[n.id]) {
          var mc = ["is-merged"].concat(fresh);
          var mcells = null;
          if (side) {
            mc.push("is-src");
            mcells = srcCls(live, side);
          }
          s += boxSVG(c, my, n.sorted, mc, mcells);
        } else if (live && live.nodeId === n.id) {
          var partial = [],
            fillCls = [];
          for (var t = 0; t < n.size; t++) {
            partial.push(t < live.out.length ? live.out[t] : null);
            fillCls.push(t < live.out.length ? "filled" : "");
          }
          s += boxSVG(c, my, partial, ["is-target"], fillCls);
        } else {
          s += ghostSVG(c, my, n.size);
        }
      }
    });

    var svg = $("tree");
    svg.setAttribute("viewBox", "0 0 " + G.W + " " + G.H);
    svg.innerHTML = s;
  }

  var BADGES = {
    start: "Start",
    divide: "Divide",
    base: "Base case",
    "merge-start": "Merge",
    compare: "Compare",
    copy: "Copy rest",
    "merge-done": "Merged",
    done: "Done",
  };

  function chips(vals, cls, ptrs) {
    return vals
      .map(function (v, t) {
        var c = (cls && cls[t]) || "";
        var p = ptrs && ptrs[t] ? '<i class="ptr">' + ptrs[t] + "</i>" : "";
        return '<span class="chip ' + c + '">' + v + p + "</span>";
      })
      .join("");
  }

  function renderWorkspace(S) {
    var h = "";
    var m = S.merge;
    if (m) {
      var Lp = {},
        Rp = {};
      if (m.kind === "start") {
        Lp[0] = "i";
        Rp[0] = "j";
      }
      if (m.kind === "compare") {
        Lp[m.li] = "i";
        Rp[m.rj] = "j";
      }
      var total = m.L.length + m.R.length;
      var outCls = m.out.map(function () {
        return "taken";
      });
      var empties = "";
      for (var e = m.out.length; e < total; e++) {
        empties += '<span class="chip empty"></span>';
      }
      h +=
        '<div class="ws-row"><span class="ws-label">Left</span><div class="chiprow">' +
        chips(m.L, srcCls(m, "L"), Lp) +
        "</div></div>";
      h +=
        '<div class="ws-row"><span class="ws-label">Right</span><div class="chiprow">' +
        chips(m.R, srcCls(m, "R"), Rp) +
        "</div></div>";
      h +=
        '<div class="ws-row"><span class="ws-label">Output</span><div class="chiprow">' +
        chips(m.out, outCls) +
        empties +
        "</div></div>";
      h +=
        '<p class="ws-note">i and j point to the front of the left and right half.</p>';
    } else if (S.kind === "divide") {
      var n = nodes[S.active];
      h +=
        '<div class="ws-row"><div class="chiprow">' +
        chips(n.left.vals) +
        '<span class="splitbar"></span>' +
        chips(n.right.vals) +
        "</div></div>";
      h +=
        '<p class="ws-note">Left half = A[' +
        n.lo +
        ".." +
        n.mid +
        "], right half = A[" +
        (n.mid + 1) +
        ".." +
        n.hi +
        "].</p>";
    } else if (S.kind === "base") {
      var b = nodes[S.active];
      h +=
        '<div class="ws-row"><div class="chiprow">' +
        chips(b.vals, ["leaf"]) +
        "</div></div>";
      h += '<p class="ws-note">One element: nothing to sort.</p>';
    } else if (S.kind === "done") {
      h +=
        '<div class="ws-row"><div class="chiprow">' +
        chips(
          root.sorted,
          root.sorted.map(function () {
            return "taken";
          }),
        ) +
        "</div></div>";
      h += '<p class="ws-note">The array is now sorted in ascending order.</p>';
    } else {
      h +=
        '<div class="ws-row"><div class="chiprow">' +
        chips(arr) +
        "</div></div>";
      h += '<p class="ws-note">Unsorted input array.</p>';
    }
    $("workspace").innerHTML = h;
  }

  function renderLog() {
    $("log").innerHTML = steps
      .map(function (s, i) {
        return '<li data-i="' + i + '">' + s.text + "</li>";
      })
      .join("");
  }
  function updateLog() {
    var items = $("log").children;
    for (var i = 0; i < items.length; i++) {
      items[i].className = i < cur ? "past" : i === cur ? "current" : "";
    }
    var li = items[cur];
    if (li) {
      var box = $("log");
      box.scrollTop = Math.max(
        0,
        li.offsetTop - box.clientHeight / 2 + li.clientHeight / 2,
      );
    }
  }

  function render() {
    var st = stateAt(cur);
    var S = steps[cur];
    renderTree(st);
    renderWorkspace(S);

    $("explain").innerHTML =
      '<span class="badge ' +
      S.kind +
      '">' +
      BADGES[S.kind] +
      "</span><p>" +
      S.text +
      "</p>";

    var lis = $("pseudo").children;
    for (var i = 0; i < lis.length; i++) {
      var ln = Number(lis[i].getAttribute("data-l"));
      lis[i].className = S.line.indexOf(ln) >= 0 ? "hl" : "";
    }

    $("stepNo").textContent = cur + 1;
    $("stepTotal").textContent = steps.length;
    $("cmpNow").textContent = S.cmp;
    $("cmpTotal").textContent = totalCmp;
    $("progressBar").style.width =
      (steps.length > 1 ? (cur / (steps.length - 1)) * 100 : 100) + "%";
    $("btnPrev").disabled = cur === 0;
    $("btnNext").disabled = cur === steps.length - 1;
    updateLog();
    renderStats();
  }

  function bestCmp(n) {
    return n <= 1
      ? 0
      : bestCmp(Math.ceil(n / 2)) +
          bestCmp(Math.floor(n / 2)) +
          Math.floor(n / 2);
  }
  function worstCmp(n) {
    return n <= 1
      ? 0
      : worstCmp(Math.ceil(n / 2)) + worstCmp(Math.floor(n / 2)) + n - 1;
  }

  var CASES = {
    best: {
      name: "Best case",
      big: "O(n log n)",
      why:
        "Happens when every element of the left half is already smaller than the right half (for example an already sorted array). " +
        "Each merge ends as soon as one half is used up, so only about n/2 comparisons are needed per level. " +
        "The array is still split into log n levels and all n elements are still copied at every level, so the total time stays n log n.",
      cmp: "About (n / 2) × log₂ n comparisons.",
    },
    avg: {
      name: "Average case",
      big: "O(n log n)",
      why:
        "For a random order the halves interleave. Each merge needs a bit less than n − 1 comparisons, roughly n log₂ n − 1.25 n comparisons in total. " +
        "With log n levels and n elements handled per level the time is n log n.",
      cmp: "About n × log₂ n − 1.25 n comparisons.",
    },
    worst: {
      name: "Worst case",
      big: "O(n log n)",
      why:
        "Happens when the two halves interleave perfectly (for example 1 5 2 6 …), so neither half runs out early and a merge of n elements needs n − 1 comparisons. " +
        "This is still only n log n in total, unlike Quick Sort whose worst case is O(n²).",
      cmp: "About n × log₂ n − n + 1 comparisons.",
    },
  };

  function showCase(key) {
    var c = CASES[key];
    $("casePanel").innerHTML =
      '<p class="big-o">' +
      c.big +
      "<small>" +
      c.name +
      "</small></p>" +
      "<p>" +
      c.why +
      "</p>" +
      "<p><b>" +
      c.cmp +
      "</b></p>" +
      "<p><b>Space complexity:</b> O(n) for the temporary merge array.</p>";
    var tabs = document.querySelectorAll(".tab");
    for (var i = 0; i < tabs.length; i++) {
      tabs[i].setAttribute(
        "aria-selected",
        tabs[i].getAttribute("data-case") === key ? "true" : "false",
      );
    }
  }

  function renderLevelTable() {
    var rows = "",
      totalEl = 0,
      totalMerges = 0;
    for (var d = D - 1; d >= 0; d--) {
      var at = nodes.filter(function (n) {
        return n.depth === d && !n.leaf;
      });
      var elems = at.reduce(function (a, n) {
        return a + n.size;
      }, 0);
      totalEl += elems;
      totalMerges += at.length;
      rows +=
        "<tr><td>" +
        d +
        "</td><td>" +
        at.length +
        "</td><td>" +
        elems +
        "</td></tr>";
    }
    if (!rows) {
      rows = '<tr><td colspan="3">Nothing to merge for one element.</td></tr>';
    }
    document.querySelector("#levelTable tbody").innerHTML = rows;
    var foot = document.querySelector("#levelTable tfoot");
    if (foot) {
      foot.remove();
    }
    var tf = document.createElement("tfoot");
    tf.innerHTML =
      "<tr><td>Total</td><td>" +
      totalMerges +
      "</td><td>" +
      totalEl +
      "</td></tr>";
    $("levelTable").appendChild(tf);
    $("levelNote").textContent =
      "n = " +
      arr.length +
      " elements and " +
      D +
      " merge level" +
      (D === 1 ? "" : "s") +
      ", so the merging touches about n × log₂ n = " +
      totalEl +
      " element positions.";
  }

  function renderStats() {
    var n = arr.length;
    $("stats").innerHTML =
      '<div class="stat"><b>' +
      n +
      "</b><span>Elements (n)</span></div>" +
      '<div class="stat"><b>' +
      totalCmp +
      "</b><span>Comparisons made for this array</span></div>" +
      '<div class="stat"><b>' +
      bestCmp(n) +
      "</b><span>Fewest possible for n = " +
      n +
      "</span></div>" +
      '<div class="stat"><b>' +
      worstCmp(n) +
      "</b><span>Most possible for n = " +
      n +
      "</span></div>";
  }

  function go(k) {
    cur = Math.max(0, Math.min(steps.length - 1, k));
    render();
  }
  function delay() {
    return 1700 - Number($("speed").value) * 150;
  }
  function stop() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
    $("btnPlay").innerHTML = "▶ Play";
  }
  function tick() {
    if (cur >= steps.length - 1) {
      stop();
      return;
    }
    go(cur + 1);
    timer = setTimeout(tick, delay());
  }
  function play() {
    if (timer) {
      stop();
      return;
    }
    if (cur >= steps.length - 1) {
      go(0);
    }
    $("btnPlay").innerHTML = "⏸ Pause";
    timer = setTimeout(tick, delay());
  }

  function load(a) {
    stop();
    arr = a.slice();
    mode = $("modeSel").value;
    buildTree(arr);
    layout();
    genSteps();
    renderLog();
    renderLevelTable();
    $("arrInput").value = arr.join(", ");
    $("log").scrollTop = 0;
    go(0);
  }

  function parseInput(text) {
    var parts = text.split(/[\s,;]+/).filter(function (p) {
      return p.length;
    });
    if (!parts.length) {
      return { error: "Please enter at least one number." };
    }
    var out = [];
    for (var i = 0; i < parts.length; i++) {
      if (!/^-?\d+$/.test(parts[i])) {
        return {
          error:
            '"' +
            parts[i] +
            '" is not a whole number. Use numbers separated by commas or spaces.',
        };
      }
      var v = parseInt(parts[i], 10);
      if (Math.abs(v) > 999) {
        return {
          error:
            "Please keep each number between -999 and 999 so the boxes stay readable.",
        };
      }
      out.push(v);
    }
    if (out.length > MAX_N) {
      return {
        error:
          "Please enter at most " +
          MAX_N +
          " numbers so the diagram stays readable.",
      };
    }
    return { values: out };
  }

  function setMsg(text, info) {
    var el = $("inputMsg");
    el.textContent = text || "";
    el.className = "msg" + (info ? " info" : "");
  }

  function init() {
    $("inputForm").addEventListener("submit", function (ev) {
      ev.preventDefault();
      var r = parseInput($("arrInput").value);
      if (r.error) {
        setMsg(r.error);
        return;
      }
      setMsg("");
      load(r.values);
    });
    $("btnRandom").addEventListener("click", function () {
      var n = 8,
        a = [];
      for (var i = 0; i < n; i++) {
        a.push(1 + Math.floor(Math.random() * 99));
      }
      setMsg("");
      load(a);
    });
    $("modeSel").addEventListener("change", function () {
      load(arr);
    });
    $("btnNext").addEventListener("click", function () {
      stop();
      go(cur + 1);
    });
    $("btnPrev").addEventListener("click", function () {
      stop();
      go(cur - 1);
    });
    $("btnReset").addEventListener("click", function () {
      stop();
      go(0);
    });
    $("btnPlay").addEventListener("click", play);
    $("log").addEventListener("click", function (ev) {
      var li = ev.target.closest("li");
      if (li) {
        stop();
        go(Number(li.getAttribute("data-i")));
      }
    });
    document.querySelectorAll(".tab").forEach(function (t) {
      t.addEventListener("click", function () {
        showCase(t.getAttribute("data-case"));
      });
    });
    document.addEventListener("keydown", function (ev) {
      var tag = ev.target && ev.target.tagName;
      if (tag === "INPUT" || tag === "SELECT" || tag === "TEXTAREA") {
        return;
      }
      if (ev.key === "ArrowRight") {
        stop();
        go(cur + 1);
      } else if (ev.key === "ArrowLeft") {
        stop();
        go(cur - 1);
      } else if (ev.key === " " && tag !== "BUTTON") {
        ev.preventDefault();
        play();
      }
    });

    showCase("avg");

    var start = DEFAULT_ARR;
    try {
      var q = new URLSearchParams(window.location.search).get("arr");
      if (q) {
        var r = parseInput(q);
        if (r.values) {
          start = r.values;
        } else if (/at most/.test(r.error || "")) {
          var all = q
            .split(/[\s,;]+/)
            .filter(function (p) {
              return /^-?\d+$/.test(p);
            })
            .map(Number);
          start = all.slice(0, MAX_N);
          setMsg(
            "Your array has more than " +
              MAX_N +
              " numbers, so only the first " +
              MAX_N +
              " are shown.",
            true,
          );
        } else {
          setMsg(r.error + " Showing the default array instead.");
        }
      }
    } catch (e) {}
    load(start);
  }

  init();
})();
