import {
    Popover,
    PopoverTrigger,
    PopoverContent,
    PopoverBody,
    PopoverArrow,
    PopoverCloseButton,
    useDisclosure,
    PopoverHeader
  } from '@chakra-ui/react'
  import { InfoOutlineIcon } from '@chakra-ui/icons'


  export type InfoPopoverPropsType = {
    info: string;
    title: string;
    ml : string;
  }

  const InfoPopover = (props: InfoPopoverPropsType) => {
    const {info,title,ml} = props;
    return(
    <Popover  placement='bottom-start' trigger="hover">
        <PopoverTrigger>
            <InfoOutlineIcon style={{marginLeft:ml}}/>
        </PopoverTrigger>
        <PopoverContent >
            {title !== "" &&<PopoverHeader fontWeight='semibold'>{title}</PopoverHeader>}
            <PopoverArrow />
            <PopoverCloseButton />
            <PopoverBody>
                {info}
            </PopoverBody>
        </PopoverContent>
    </Popover>
  )
  }

  export default InfoPopover;