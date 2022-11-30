import { Box, Button } from "@chakra-ui/react"

/**  
 * Replaces symbol textbox with button.
 * Upon click copies the symbol displayed in the button to the clipboard.
 * Useful for when iProve symbol is not present on someone's keyboard
 */
export const SymbolButton = (props: {symbol: string}) => {
    return (
        <Box>
            <Button className="symbol-buttons" onClick={() => navigator.clipboard.writeText(props.symbol)} style={{ backgroundColor: "antiquewhite" }}>
                { props.symbol }
            </Button>
        </Box>
    )
}