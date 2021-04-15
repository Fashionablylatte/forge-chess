d3.selectAll("svg > *").remove();

function printValue(row, col, xoffset, yoffset, value) {
  d3.select(svg)
    .append("text")
    .style("fill", "black")
    .attr("x", row*75 + xoffset)
    .attr("y", col*75 + yoffset)
    .attr("font-size", "xx-large")
    .text(value);
}

function convert(square) {
  const squareContent = square.pc.toString()
  console.log(squareContent)
  if(squareContent == '') {
    return '_'
  } else {
    return squareContent
  }
}

function toCoord(rc) {
  return rc.charAt(3);
}

// printValue(row1, colA, 5, 25, Board0.places[row1][colA])

function printBoard(startRow, startCol, board) {
  let row = startRow;
  let col = startCol;

  
  for (r = 0; r < 8; r++) {
    printValue(0, r, 50, 50, toCoord(row.toString()));
    for (c = 1; c < 9; c++) {
      const square = Board0.places[row][col];
      printValue(c, r, 50, 50, convert(square));
//       printValue(c, r, 50, 50, square.coord.toString())
//       console.log(convert(square));
      col = col.c_next;
    }
    col = startCol;
    row = row.r_prev;
  }
  
  for (c = 1; c < 9; c++){
    printValue(c, 8, 50, 50, toCoord(col.toString()));
    col = col.c_next;
  }
  
}

printBoard(row8, colA, Board0);
