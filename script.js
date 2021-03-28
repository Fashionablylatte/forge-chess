d3.selectAll("svg > *").remove();

function printValue(row, col, xoffset, yoffset, value) {
  d3.select(svg)
    .append("text")
    .style("fill", "black")
    .attr("x", row*25 + xoffset)
    .attr("y", col*36 + yoffset)
    .attr("font-size", "xx-large")
    .text(value);
}

function convert(value) {
  const str = value.toString().substring(0, 1);
  if(str == ''){
    return '_'
  } else {
    return str
  }
}

function printBoard(boardAtom, xoffset, yoffset) {
  let colSort = orderCols()
  let rowSort = orderRows()
  for (r = 0; r < rowSort.length; r++) {
    for (c = 0; c < colSort.length; c++) {
      console.log([rowSort[r]].toString() + ", " + [colSort[c]].toString() + " = " + convert(boardAtom.places[rowSort[r]][colSort[c]]))
      printValue(r, c, xoffset, yoffset,
                 convert(boardAtom.places[rowSort[r]][colSort[c]]))  
    }
  }   
}

function orderRows(){
  let ra = []
  let rmap = new Map()
  let rns = row_neighbors.tuples()
  for(n = 0; n < rns.length; n++){
    tup = rns[n].atoms()
    curr = rmap.get(tup[0])
    if(curr != undefined){
      curr.push(tup[1])
      rmap.set(tup[0], curr)
    } else {
      rmap.set(tup[0], [tup[1]])
    }
  }
  let first_entry;
  for(let [key, value] of rmap.entries()){
    if(value.length == 2){
      first_entry = [key, value]
    } else if(value.length == 1){
      ra.push(key)
      return ra
    }
  }
  
  let r_prev = first_entry[0]
  let r_curr = first_entry[1].find(e => e != r_prev)
  ra.push(r_prev)
  ra.push(r_curr)
  while(true){
    let crt = rmap.get(r_curr)
    if(crt.length == 2){
      break
    } else {
      let newr = crt.find(e => e != r_prev && e != r_curr)
      ra.push(newr)
      r_prev = r_curr
      r_curr = newr
    }
  }
  return ra
}

function orderCols() {
  let ca = []
  let cmap = new Map()
  let cns = col_neighbors.tuples()
  for(m = 0; m < cns.length; m++){
      tup = cns[m].atoms()
      curr = cmap.get(tup[0])
      if(curr != undefined){
        curr.push(tup[1])
        cmap.set(tup[0], curr)
      } else {
        cmap.set(tup[0], [tup[1]])
      }
    }
  let first_entry;
  for(let [key, value] of cmap.entries()){
    if(value.length == 2){
      first_entry = [key, value]
    } else if(value.length == 1){
      ca.push(key)
      return ca
    }
  }
  
  let c_prev = first_entry[0]
  let c_curr = first_entry[1].find(e => e != c_prev)
  ca.push(c_prev)
  ca.push(c_curr)
  while(true){
    let cct = cmap.get(c_curr)
    if(cct.length == 2){
      break
    } else {
      let newc = cct.find(e => e != c_prev && e != c_curr)
      ca.push(newc)
      c_prev = c_curr
      c_curr = newc
    }
  }
  return ca
}

printBoard(Board0, 5, 25)
