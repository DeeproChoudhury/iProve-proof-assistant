import { Stack, Button, Popover, PopoverTrigger, PopoverContent, PopoverArrow, PopoverCloseButton, PopoverBody, TableContainer, Table, Thead, Tr, Th, Tbody, Td } from "@chakra-ui/react"
import { useIProveStore } from "../store/store"
import { SymbolButton } from "./SymbolButton"

const Header = () => {
  /* Table used to display 'help' information to user */
  const operatorsToSymbols = [{ value: 'and', symbol: '&' },
  { value: 'or', symbol: '||' },
  { value: 'iff', symbol: '<->' },
  { value: 'implies', symbol: '->' },
  { value: 'for all x', symbol: 'FA x.' },
  { value: 'exists x', symbol: 'EX x.' },
  { value: 'negation', symbol: '~' },
  { value: 'x ∈ S', symbol: 'x in S' }]
  
  const actions = useIProveStore(store => store.actions);
  const uiShown = useIProveStore(store => store.uiShown);

  return (

    <div className='header'>

      <span className="emBox">
        <span className='highlight'>i</span>Prove
      </span>

      <Stack spacing={4} direction='row' align='center' overflow='scroll' style={{marginLeft: '20px'}}>

        <Button className="headButton" variant="outline" colorScheme='purple' onClick={actions.global.addGivenNode}>Add Given</Button>
        <Button className="headButton" variant="outline" colorScheme='purple' onClick={actions.global.addGoalNode}>Add Goal</Button>
        <Button className="headButton" variant="outline" colorScheme='purple' onClick={actions.global.addProofNode}>Add Proof Node</Button>
        <Button className="headButton" variant="outline" colorScheme='purple' onClick={actions.global.addInductionNode}>Add Induction Node</Button>
        <Button className="headButton" variant="outline" colorScheme='purple' onClick={() => actions.global.showUI("import")}>Import Proofs</Button>
        <Button className="headButton" variant="outline" colorScheme='purple' onClick={() => actions.global.showUI("export")}>
          Export proof
        </Button>
        <Button className="headButton" variant="outline" colorScheme='purple' onClick={() => actions.global.showUI("addReasons")}>
          Verify Entire Proof
        </Button>
        <Button className="headButton" variant="outline" colorScheme='purple' onClick={() => actions.global.toggleUI("sidebar")}>
          {uiShown.sidebar ? "Hide Sidebar" : "Show Sidebar"}
        </Button>
        


        {/* START: display table mapping symbol to iprove syntax */}
        <Popover>
          <PopoverTrigger>
            <Button className="headButton" variant="outline" colorScheme='whatsapp'>Symbols</Button>
          </PopoverTrigger>
          <PopoverContent style={{ width: "400px" }}>
            <PopoverArrow />
            <PopoverCloseButton />
            <PopoverBody>
              <TableContainer>
                <Table variant='simple'>
                  <Thead>
                    <Tr>
                      <Th>Logical Operator</Th>
                      <Th>iProve Symbol</Th>
                    </Tr>
                  </Thead>
                  <Tbody>
                    {operatorsToSymbols.map((p, index) => {
                      return <Tr key={index}>
                              <Td>{p.value}</Td>
                              <Td><SymbolButton symbol={p.symbol} /></Td>
                            </Tr>;
                    })}
                  </Tbody>
                </Table>
              </TableContainer>
            </PopoverBody>
          </PopoverContent>
        </Popover>
        {/* END: display table mapping symbol to iProve syntax */}

        <Button className="headButton" variant="outline" colorScheme='whatsapp' onClick={
            () => { window!.open("guidebook.html", '_blank')!.focus() }
          }>
          View Guide
        </Button>


      </Stack>
    </div>
  )
}

export default Header;
