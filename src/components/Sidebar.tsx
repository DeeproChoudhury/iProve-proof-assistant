import { Box, Grid, GridItem } from "@chakra-ui/react"
import React, { useRef, useState, useEffect } from "react"
import Declarations from "./Declarations"
import TypeDeclarations from "./TypeDeclarations"
import './Sidebar.css';
import { useIProveStore } from "../store/store";

const Sidebar = () => {
  const visible = useIProveStore(store => store.uiShown.sidebar);
  const sidebarRef = useRef<HTMLInputElement>(null);
  const [isResizing, setIsResizing] = useState(false);
  const [sidebarWidth, setSidebarWidth] = useState(268);

  const startResizing = React.useCallback((mouseDownEvent: any) => {
    setIsResizing(true);
  }, []);

  const stopResizing = React.useCallback(() => {
    setIsResizing(false);
  }, []);

  const resize = React.useCallback(
    (mouseMoveEvent: { clientX: number }) => {
      let value;
      if (sidebarRef.current === null) {
        value = 0;
      } else {
        value = sidebarRef.current.getBoundingClientRect().left;
      }
      if (isResizing && mouseMoveEvent.clientX - value >= 200) {
        setSidebarWidth(
          mouseMoveEvent.clientX -
          value
        );
      }
    },
    [isResizing]
  );

  useEffect(() => {
    window.addEventListener("mousemove", resize);
    window.addEventListener("mouseup", stopResizing);
    return () => {
      window.removeEventListener("mousemove", resize);
      window.removeEventListener("mouseup", stopResizing);
    };
  }, [resize, stopResizing]);
  return (
    <Box 
      visibility={visible ? "visible" : "hidden"}
      style={{
        display: 'flex', 
        flexDirection: 'row', 
        minWidth: "200px",
        marginTop: "12vh",
        marginBottom: "3vh",
        marginLeft: "3vh",
        width: sidebarWidth}}
      className="app-sidebar">
      <Grid
        gap={3}
        style={{
          zIndex: 20 /* zIndex to move column to front*/,
          backgroundColor: "#1a29ff4b",
          width: sidebarWidth,
        }}
        visibility={visible ? "visible" : "hidden"}
        ref={sidebarRef}
      >

        {/* START : General Declarations */}
        <GridItem style={{ width: "inherit" }}>
          <Declarations />
        </GridItem>
        {/* END : General Declarations */}

        {/* START : Type Declarations */}
        <GridItem style={{ width: "inherit" }}>
          <TypeDeclarations />
        </GridItem>
        {/* END : Type Declarations */}
      </Grid>
      <div style={{width: '10px'}} className="app-sidebar-resizer" onMouseDown={startResizing} />
    </Box>
  )
}

export default Sidebar;
