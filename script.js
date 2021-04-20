d3.selectAll("svg > *").remove();

const BOARD_SIZE = 5;
const OFFSET = 50;

function printValue(row, col, xoffset, yoffset, value) {
    switch(value) {
      case "BN0":
      case "BN1":
        d3.select(svg)
            .append("text")
            .style("fill", "black")
            .attr("x", row*75 + xoffset)
            .attr("y", col*75 + yoffset)
            .attr("font-size", "xxx-large")
            .text("\u265e");
        break;
      case "WN0":
      case "WN1":
        d3.select(svg)
            .append("text")
            .style("fill", "black")
            .attr("x", row*75 + xoffset)
            .attr("y", col*75 + yoffset)
            .attr("font-size", "xxx-large")
            .text("\u2658");
        break;
      case "WR0":
      case "WR1":
        d3.select(svg)
            .append("text")
            .style("fill", "black")
            .attr("x", row*75 + xoffset)
            .attr("y", col*75 + yoffset)
            .attr("font-size", "xxx-large")
            .text("\u2656");
        break;
      case "BR0":
      case "BR1":
        d3.select(svg)
            .append("text")
            .style("fill", "black")
            .attr("x", row*75 + xoffset)
            .attr("y", col*75 + yoffset)
            .attr("font-size", "xxx-large")
            .text("\u265c");
        break;
      case "BB0":
      case "BB1":
        d3.select(svg)
            .append("text")
            .style("fill", "black")
            .attr("x", row*75 + xoffset)
            .attr("y", col*75 + yoffset)
            .attr("font-size", "xxx-large")
            .text("\u265d");
        break;
      case "WB0":
      case "WB1":
        d3.select(svg)
            .append("text")
            .style("fill", "black")
            .attr("x", row*75 + xoffset)
            .attr("y", col*75 + yoffset)
            .attr("font-size", "xxx-large")
            .text("\u2657");
        break;
      case "WQ0":
      case "WQ1":
        d3.select(svg)
            .append("text")
            .style("fill", "black")
            .attr("x", row*75 + xoffset)
            .attr("y", col*75 + yoffset)
            .attr("font-size", "xxx-large")
            .text("\u2655");
        break;
      case "BQ0":
      case "BQ1":
        d3.select(svg)
            .append("text")
            .style("fill", "black")
            .attr("x", row*75 + xoffset)
            .attr("y", col*75 + yoffset)
            .attr("font-size", "xxx-large")
            .text("\u265b");
        break;
      case "WK0":
      case "WK1":
        d3.select(svg)
            .append("text")
            .style("fill", "black")
            .attr("x", row*75 + xoffset)
            .attr("y", col*75 + yoffset)
            .attr("font-size", "xxx-large")
            .text("\u2654");
        break;
      case "BK0":
      case "BK1":
        d3.select(svg)
            .append("text")
            .style("fill", "black")
            .attr("x", row*75 + xoffset)
            .attr("y", col*75 + yoffset)
            .attr("font-size", "xxx-large")
            .text("\u265a");
        break;
      case "WP0":
      case "WP1":
        d3.select(svg)
            .append("text")
            .style("fill", "black")
            .attr("x", row*75 + xoffset)
            .attr("y", col*75 + yoffset)
            .attr("font-size", "xxx-large")
            .text("\u2659");
        break;
      case "BP0":
      case "BP1":
        d3.select(svg)
            .append("text")
            .style("fill", "black")
            .attr("x", row*75 + xoffset)
            .attr("y", col*75 + yoffset)
            .attr("font-size", "xxx-large")
            .text("\u265f");
         break;
      default:
          d3.select(svg)
            .append("text")
            .style("fill", "black")
            .attr("x", row*75 + xoffset)
            .attr("y", col*75 + yoffset)
            .attr("font-size", "xxx-large")
            .text(value);
  }
}

function convert(square) {
  const precontent = square.join(pc)
  let content = ''
  if ((Black0.pieces).join(precontent).empty()) {
    content = 'W' + precontent.toString()
  } else {
    content = 'B' + precontent.toString()
  }
  if (precontent.empty()) {
    return '-'
  } else {
    return content.toString()
  }
}

function toCoord(rc) {
  return rc.charAt(3);
}

function printBoard(startRow, startCol) {
  let row = startRow;
  let col = startCol;
  
  for (r = 0; r < BOARD_SIZE; r++) {
    printValue(0, r, OFFSET, OFFSET, toCoord(row.toString()));
    for (c = 1; c < BOARD_SIZE + 1; c++) {
      const square = coord.join(col).join(row)
      printValue(c, r, OFFSET, OFFSET, convert(square));
      col = col.c_next;
    }
    col = startCol;
    row = row.r_prev;
  }
  
  for (c = 1; c < BOARD_SIZE + 1; c++) {
    printValue(c, BOARD_SIZE, OFFSET, OFFSET, toCoord(col.toString()));
    col = col.c_next;
  }
  
}
printBoard(row5, colA)