import { CloseIcon } from "@chakra-ui/icons";
import { Alert, AlertDescription, AlertIcon, AlertTitle, IconButton } from "@chakra-ui/react";
import { useIProveStore } from "../store/store";
import { IProveError } from "../types/ErrorLocation";
import { renderError } from "../util/errors";

export default function Alerts() {
  const actions = useIProveStore(draft => draft.actions);
  const alerts = [useIProveStore(draft => draft.error)]; // TODO: add support for multiple errors elsewhere

  return <>{alerts.filter((alert): alert is IProveError => !!alert).map(alert => {
    const [status, title, description] = alert.status === "success" ? [
      "success",
      "Success!",
      alert.msg ?? "",
    ] as const : [
      "error",
      alert.kind ? `${alert.kind} Error!` : "Error!",
      renderError(alert),
    ] as const;
    return <div className="alert-container">
      <Alert className="alert" status={status}>
        <AlertIcon />
        <AlertTitle>{title}</AlertTitle>
        <AlertDescription>{description}</AlertDescription>
        <IconButton
          variant='outline'
          aria-label='Close popup'
          size='xs'
          onClick={actions.global.resetError}
          icon={<CloseIcon />}
        />
      </Alert>
    </div>
  })}</>;
}
