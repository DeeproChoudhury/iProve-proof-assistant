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
  }

  const InfoPopover = (props: InfoPopoverPropsType) => {
    const {info,title} = props;
    return(
    <Popover placement='bottom-start' trigger="hover">
        <PopoverTrigger>
            <InfoOutlineIcon />
        </PopoverTrigger>
        <PopoverContent>
            <PopoverHeader fontWeight='semibold'>{title}</PopoverHeader>
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